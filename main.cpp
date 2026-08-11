#include <array>
#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <fcntl.h>
#include <iostream>
#include <limits>
#include <list>
#include <memory>
#include <stdexcept>
#include <string>
#include <sys/stat.h>
#include <system_error>
#include <unistd.h>
#include <unordered_map>

namespace {

constexpr std::size_t PAGE_SIZE = 4096;
constexpr std::size_t MAX_KEYS = 52;
constexpr std::size_t MIN_KEYS = MAX_KEYS / 2;
constexpr std::size_t CACHE_CAPACITY = 1024;

constexpr std::uint32_t NODE_MAGIC = 0x4250544EU;
constexpr std::uint32_t FREE_NODE_MAGIC = 0x46524545U;
constexpr std::uint32_t FILE_VERSION = 1;

constexpr char FILE_MAGIC[8] = {
    'B', 'P', 'T', '0', '1', '6', 'D', 'B'
};

struct Key {
    char index[65];
    std::int32_t value;
};

static_assert(sizeof(Key) == 72);

struct LeafData {
    Key keys[MAX_KEYS];
};

struct InternalData {
    Key keys[MAX_KEYS];
    std::uint32_t children[MAX_KEYS + 1];
};

union NodeData {
    LeafData leaf;
    InternalData internal;
};

struct NodeHeader {
    std::uint32_t magic;
    std::uint32_t self;
    std::uint32_t parent;
    std::uint32_t next;
    std::uint32_t previous;
    std::uint16_t count;
    std::uint8_t is_leaf;
    std::uint8_t reserved;
};

static_assert(sizeof(NodeHeader) == 24);
static_assert(sizeof(NodeData) == 3956);

struct Node {
    NodeHeader header;
    NodeData data;
    std::array<std::byte,
               PAGE_SIZE - sizeof(NodeHeader) - sizeof(NodeData)> padding;
};

static_assert(sizeof(Node) == PAGE_SIZE);

struct Metadata {
    char magic[8];
    std::uint32_t version;
    std::uint32_t page_size;
    std::uint32_t root;
    std::uint32_t first_leaf;
    std::uint32_t next_page;
    std::uint32_t free_head;
    std::array<std::byte,
               PAGE_SIZE - 8 - 6 * sizeof(std::uint32_t)> padding;
};

static_assert(sizeof(Metadata) == PAGE_SIZE);

int compareKeys(const Key &left, const Key &right) {
    const int index_comparison = std::strcmp(left.index, right.index);
    if (index_comparison != 0) {
        return index_comparison;
    }

    if (left.value < right.value) {
        return -1;
    }
    if (left.value > right.value) {
        return 1;
    }
    return 0;
}

int compareIndex(const Key &key, const std::string &index) {
    return std::strcmp(key.index, index.c_str());
}

Key makeKey(const std::string &index, std::int32_t value) {
    if (index.size() > 64) {
        throw std::runtime_error("Index exceeds 64 bytes");
    }

    Key key{};
    std::memcpy(key.index, index.data(), index.size());
    key.index[index.size()] = '\0';
    key.value = value;
    return key;
}

class PageFile {
public:
    explicit PageFile(const std::string &path) {
        file_descriptor_ = ::open(path.c_str(), O_RDWR | O_CREAT, 0644);
        if (file_descriptor_ < 0) {
            throwSystemError("Unable to open database file");
        }

        try {
            struct stat file_stat {};
            if (::fstat(file_descriptor_, &file_stat) != 0) {
                throwSystemError("Unable to inspect database file");
            }

            if (file_stat.st_size == 0) {
                initializeMetadata();
                writeExact(0, &metadata_, sizeof(metadata_));
            } else {
                if (file_stat.st_size < static_cast<off_t>(PAGE_SIZE)) {
                    throw std::runtime_error("Database metadata is truncated");
                }

                readExact(0, &metadata_, sizeof(metadata_));
                validateMetadata();
            }
        } catch (...) {
            ::close(file_descriptor_);
            file_descriptor_ = -1;
            throw;
        }
    }

    PageFile(const PageFile &) = delete;
    PageFile &operator=(const PageFile &) = delete;

    ~PageFile() {
        if (file_descriptor_ >= 0) {
            try {
                flush();
            } catch (...) {
            }
            ::close(file_descriptor_);
        }
    }

    Metadata &metadata() {
        return metadata_;
    }

    Node &get(std::uint32_t page_id) {
        auto found = cache_.find(page_id);
        if (found != cache_.end()) {
            touch(*found->second);
            return found->second->page;
        }

        ensureCacheSpace();

        auto entry = std::make_unique<CacheEntry>();
        readExact(pageOffset(page_id), &entry->page, sizeof(Node));

        lru_.push_front(page_id);
        entry->lru_position = lru_.begin();

        Node &result = entry->page;
        cache_.emplace(page_id, std::move(entry));
        return result;
    }

    Node &reset(std::uint32_t page_id) {
        auto found = cache_.find(page_id);
        if (found != cache_.end()) {
            touch(*found->second);
            found->second->page = Node{};
            found->second->dirty = true;
            return found->second->page;
        }

        ensureCacheSpace();

        auto entry = std::make_unique<CacheEntry>();
        entry->page = Node{};
        entry->dirty = true;

        lru_.push_front(page_id);
        entry->lru_position = lru_.begin();

        Node &result = entry->page;
        cache_.emplace(page_id, std::move(entry));
        return result;
    }

    void markDirty(std::uint32_t page_id) {
        auto found = cache_.find(page_id);
        if (found == cache_.end()) {
            throw std::runtime_error("Attempted to dirty an uncached page");
        }

        found->second->dirty = true;
        touch(*found->second);
    }

    void flush() {
        for (auto &item : cache_) {
            flushEntry(item.first, *item.second);
        }

        writeExact(0, &metadata_, sizeof(metadata_));
    }

private:
    struct CacheEntry {
        Node page{};
        bool dirty = false;
        std::list<std::uint32_t>::iterator lru_position;
    };

    int file_descriptor_ = -1;
    Metadata metadata_{};
    std::list<std::uint32_t> lru_;
    std::unordered_map<std::uint32_t, std::unique_ptr<CacheEntry>> cache_;

    static off_t pageOffset(std::uint32_t page_id) {
        return static_cast<off_t>(page_id) *
               static_cast<off_t>(PAGE_SIZE);
    }

    [[noreturn]] static void throwSystemError(const std::string &message) {
        throw std::system_error(errno, std::generic_category(), message);
    }

    void initializeMetadata() {
        metadata_ = Metadata{};
        std::memcpy(metadata_.magic, FILE_MAGIC, sizeof(FILE_MAGIC));
        metadata_.version = FILE_VERSION;
        metadata_.page_size = PAGE_SIZE;
        metadata_.root = 0;
        metadata_.first_leaf = 0;
        metadata_.next_page = 1;
        metadata_.free_head = 0;
    }

    void validateMetadata() const {
        if (std::memcmp(metadata_.magic, FILE_MAGIC, sizeof(FILE_MAGIC)) != 0) {
            throw std::runtime_error("Database file has an invalid signature");
        }
        if (metadata_.version != FILE_VERSION) {
            throw std::runtime_error("Unsupported database file version");
        }
        if (metadata_.page_size != PAGE_SIZE) {
            throw std::runtime_error("Database page size is incompatible");
        }
        if (metadata_.next_page == 0) {
            throw std::runtime_error("Database metadata is invalid");
        }
    }

    void readExact(off_t offset, void *buffer, std::size_t size) {
        auto *destination = static_cast<std::byte *>(buffer);
        std::size_t completed = 0;

        while (completed < size) {
            const ssize_t result =
                ::pread(file_descriptor_,
                        destination + completed,
                        size - completed,
                        offset + static_cast<off_t>(completed));

            if (result < 0) {
                if (errno == EINTR) {
                    continue;
                }
                throwSystemError("Unable to read database file");
            }
            if (result == 0) {
                throw std::runtime_error("Unexpected end of database file");
            }

            completed += static_cast<std::size_t>(result);
        }
    }

    void writeExact(off_t offset, const void *buffer, std::size_t size) {
        const auto *source = static_cast<const std::byte *>(buffer);
        std::size_t completed = 0;

        while (completed < size) {
            const ssize_t result =
                ::pwrite(file_descriptor_,
                         source + completed,
                         size - completed,
                         offset + static_cast<off_t>(completed));

            if (result < 0) {
                if (errno == EINTR) {
                    continue;
                }
                throwSystemError("Unable to write database file");
            }
            if (result == 0) {
                throw std::runtime_error("Unable to complete database write");
            }

            completed += static_cast<std::size_t>(result);
        }
    }

    void touch(CacheEntry &entry) {
        lru_.splice(lru_.begin(), lru_, entry.lru_position);
        entry.lru_position = lru_.begin();
    }

    void flushEntry(std::uint32_t page_id, CacheEntry &entry) {
        if (!entry.dirty) {
            return;
        }

        writeExact(pageOffset(page_id), &entry.page, sizeof(Node));
        entry.dirty = false;
    }

    void ensureCacheSpace() {
        if (cache_.size() < CACHE_CAPACITY) {
            return;
        }

        const std::uint32_t page_id = lru_.back();
        auto found = cache_.find(page_id);
        if (found == cache_.end()) {
            throw std::runtime_error("Page cache is inconsistent");
        }

        flushEntry(page_id, *found->second);
        lru_.pop_back();
        cache_.erase(found);
    }
};

class BPlusTree {
public:
    explicit BPlusTree(const std::string &path)
        : file_(path) {
        if (file_.metadata().root == 0) {
            const std::uint32_t root = allocateNode(true, 0);
            file_.metadata().root = root;
            file_.metadata().first_leaf = root;
        } else {
            node(file_.metadata().root);
        }
    }

    void insert(const std::string &index, std::int32_t value) {
        const Key key = makeKey(index, value);
        const std::uint32_t leaf_id = findLeaf(key);
        Node &leaf = node(leaf_id);

        const std::size_t position = lowerBound(leaf, key);
        if (position < leaf.header.count &&
            compareKeys(leaf.data.leaf.keys[position], key) == 0) {
            return;
        }

        if (position == 0 && leaf.header.count > 0) {
            updateSubtreeMinimum(leaf_id, key);
        }

        if (leaf.header.count < MAX_KEYS) {
            for (std::size_t i = leaf.header.count; i > position; --i) {
                leaf.data.leaf.keys[i] = leaf.data.leaf.keys[i - 1];
            }
            leaf.data.leaf.keys[position] = key;
            ++leaf.header.count;
            file_.markDirty(leaf_id);
            return;
        }

        splitLeafAndInsert(leaf_id, position, key);
    }

    void erase(const std::string &index, std::int32_t value) {
        const Key key = makeKey(index, value);
        const std::uint32_t leaf_id = findLeaf(key);
        Node &leaf = node(leaf_id);

        const std::size_t position = lowerBound(leaf, key);
        if (position >= leaf.header.count ||
            compareKeys(leaf.data.leaf.keys[position], key) != 0) {
            return;
        }

        for (std::size_t i = position; i + 1 < leaf.header.count; ++i) {
            leaf.data.leaf.keys[i] = leaf.data.leaf.keys[i + 1];
        }
        --leaf.header.count;
        file_.markDirty(leaf_id);

        if (leaf_id == file_.metadata().root) {
            return;
        }

        if (position == 0 && leaf.header.count > 0) {
            updateSubtreeMinimum(leaf_id, leaf.data.leaf.keys[0]);
        }

        if (leaf.header.count < MIN_KEYS) {
            rebalanceLeaf(leaf_id);
        }
    }

    void find(const std::string &index, std::ostream &output) {
        const Key lower_key =
            makeKey(index, std::numeric_limits<std::int32_t>::min());

        std::uint32_t leaf_id = findLeaf(lower_key);
        std::size_t position = lowerBound(node(leaf_id), lower_key);
        bool found = false;

        while (leaf_id != 0) {
            Node &leaf = node(leaf_id);

            for (; position < leaf.header.count; ++position) {
                const Key &key = leaf.data.leaf.keys[position];
                const int comparison = compareIndex(key, index);

                if (comparison > 0) {
                    if (!found) {
                        output << "null";
                    }
                    output << '\n';
                    return;
                }

                if (comparison == 0) {
                    if (found) {
                        output << ' ';
                    }
                    output << key.value;
                    found = true;
                }
            }

            leaf_id = leaf.header.next;
            position = 0;
        }

        if (!found) {
            output << "null";
        }
        output << '\n';
    }

    void flush() {
        file_.flush();
    }

private:
    PageFile file_;

    Node &node(std::uint32_t page_id) {
        if (page_id == 0) {
            throw std::runtime_error("Invalid page reference");
        }

        Node &result = file_.get(page_id);
        if (result.header.magic != NODE_MAGIC ||
            result.header.self != page_id) {
            throw std::runtime_error("Database node is invalid");
        }
        return result;
    }

    std::uint32_t allocateNode(bool is_leaf, std::uint32_t parent) {
        Metadata &metadata = file_.metadata();
        std::uint32_t page_id = 0;

        if (metadata.free_head != 0) {
            page_id = metadata.free_head;
            Node &free_node = file_.get(page_id);

            if (free_node.header.magic != FREE_NODE_MAGIC ||
                free_node.header.self != page_id) {
                throw std::runtime_error("Database free list is invalid");
            }

            metadata.free_head = free_node.header.next;
        } else {
            page_id = metadata.next_page;
            ++metadata.next_page;
        }

        Node &new_node = file_.reset(page_id);
        new_node.header.magic = NODE_MAGIC;
        new_node.header.self = page_id;
        new_node.header.parent = parent;
        new_node.header.next = 0;
        new_node.header.previous = 0;
        new_node.header.count = 0;
        new_node.header.is_leaf = is_leaf ? 1 : 0;
        file_.markDirty(page_id);
        return page_id;
    }

    void releaseNode(std::uint32_t page_id) {
        Node &released = file_.reset(page_id);
        released.header.magic = FREE_NODE_MAGIC;
        released.header.self = page_id;
        released.header.next = file_.metadata().free_head;
        file_.metadata().free_head = page_id;
        file_.markDirty(page_id);
    }

    static std::size_t lowerBound(const Node &leaf, const Key &key) {
        std::size_t left = 0;
        std::size_t right = leaf.header.count;

        while (left < right) {
            const std::size_t middle = left + (right - left) / 2;
            if (compareKeys(leaf.data.leaf.keys[middle], key) < 0) {
                left = middle + 1;
            } else {
                right = middle;
            }
        }

        return left;
    }

    std::uint32_t findLeaf(const Key &key) {
        std::uint32_t current_id = file_.metadata().root;

        while (true) {
            Node &current = node(current_id);
            if (current.header.is_leaf != 0) {
                return current_id;
            }

            std::size_t child_position = 0;
            while (child_position < current.header.count &&
                   compareKeys(key,
                               current.data.internal.keys[child_position]) >= 0) {
                ++child_position;
            }

            current_id = current.data.internal.children[child_position];
        }
    }

    std::size_t childPosition(const Node &parent,
                              std::uint32_t child_id) const {
        for (std::size_t i = 0; i <= parent.header.count; ++i) {
            if (parent.data.internal.children[i] == child_id) {
                return i;
            }
        }

        throw std::runtime_error("Parent does not reference child");
    }

    void updateSubtreeMinimum(std::uint32_t node_id,
                              const Key &new_minimum) {
        std::uint32_t current_id = node_id;

        while (true) {
            Node &current = node(current_id);
            if (current.header.parent == 0) {
                return;
            }

            const std::uint32_t parent_id = current.header.parent;
            Node &parent = node(parent_id);
            const std::size_t position =
                childPosition(parent, current_id);

            if (position > 0) {
                parent.data.internal.keys[position - 1] = new_minimum;
                file_.markDirty(parent_id);
                return;
            }

            current_id = parent_id;
        }
    }

    void splitLeafAndInsert(std::uint32_t leaf_id,
                            std::size_t insertion_position,
                            const Key &key) {
        Node &leaf = node(leaf_id);
        std::array<Key, MAX_KEYS + 1> temporary_keys{};

        std::size_t old_position = 0;
        for (std::size_t i = 0; i < MAX_KEYS + 1; ++i) {
            if (i == insertion_position) {
                temporary_keys[i] = key;
            } else {
                temporary_keys[i] =
                    leaf.data.leaf.keys[old_position++];
            }
        }

        const std::size_t left_count = (MAX_KEYS + 1) / 2;
        const std::size_t right_count = MAX_KEYS + 1 - left_count;

        const std::uint32_t right_id =
            allocateNode(true, leaf.header.parent);
        Node &right = node(right_id);

        for (std::size_t i = 0; i < left_count; ++i) {
            leaf.data.leaf.keys[i] = temporary_keys[i];
        }
        leaf.header.count = static_cast<std::uint16_t>(left_count);

        for (std::size_t i = 0; i < right_count; ++i) {
            right.data.leaf.keys[i] =
                temporary_keys[left_count + i];
        }
        right.header.count = static_cast<std::uint16_t>(right_count);

        right.header.next = leaf.header.next;
        right.header.previous = leaf_id;

        if (leaf.header.next != 0) {
            Node &next_leaf = node(leaf.header.next);
            next_leaf.header.previous = right_id;
            file_.markDirty(next_leaf.header.self);
        }

        leaf.header.next = right_id;
        file_.markDirty(leaf_id);
        file_.markDirty(right_id);

        insertIntoParent(leaf_id,
                         right.data.leaf.keys[0],
                         right_id);
    }

    void insertIntoParent(std::uint32_t left_id,
                          const Key &separator,
                          std::uint32_t right_id) {
        Node &left = node(left_id);
        const std::uint32_t parent_id = left.header.parent;

        if (parent_id == 0) {
            const std::uint32_t root_id =
                allocateNode(false, 0);
            Node &root = node(root_id);

            root.header.count = 1;
            root.data.internal.keys[0] = separator;
            root.data.internal.children[0] = left_id;
            root.data.internal.children[1] = right_id;

            left.header.parent = root_id;
            Node &right = node(right_id);
            right.header.parent = root_id;

            file_.metadata().root = root_id;
            file_.markDirty(root_id);
            file_.markDirty(left_id);
            file_.markDirty(right_id);
            return;
        }

        Node &parent = node(parent_id);
        const std::size_t insertion_position =
            childPosition(parent, left_id);

        if (parent.header.count < MAX_KEYS) {
            for (std::size_t i = parent.header.count;
                 i > insertion_position;
                 --i) {
                parent.data.internal.keys[i] =
                    parent.data.internal.keys[i - 1];
            }

            for (std::size_t i = parent.header.count + 1;
                 i > insertion_position + 1;
                 --i) {
                parent.data.internal.children[i] =
                    parent.data.internal.children[i - 1];
            }

            parent.data.internal.keys[insertion_position] = separator;
            parent.data.internal.children[insertion_position + 1] = right_id;
            ++parent.header.count;

            Node &right = node(right_id);
            right.header.parent = parent_id;

            file_.markDirty(parent_id);
            file_.markDirty(right_id);
            return;
        }

        splitInternalAndInsert(parent_id,
                               insertion_position,
                               separator,
                               right_id);
    }

    void splitInternalAndInsert(std::uint32_t node_id,
                                std::size_t insertion_position,
                                const Key &separator,
                                std::uint32_t right_child_id) {
        Node &current = node(node_id);
        std::array<Key, MAX_KEYS + 1> temporary_keys{};
        std::array<std::uint32_t, MAX_KEYS + 2> temporary_children{};

        for (std::size_t i = 0; i <= insertion_position; ++i) {
            temporary_children[i] =
                current.data.internal.children[i];
        }
        temporary_children[insertion_position + 1] = right_child_id;
        for (std::size_t i = insertion_position + 1;
             i <= MAX_KEYS;
             ++i) {
            temporary_children[i + 1] =
                current.data.internal.children[i];
        }

        for (std::size_t i = 0; i < insertion_position; ++i) {
            temporary_keys[i] = current.data.internal.keys[i];
        }
        temporary_keys[insertion_position] = separator;
        for (std::size_t i = insertion_position; i < MAX_KEYS; ++i) {
            temporary_keys[i + 1] =
                current.data.internal.keys[i];
        }

        const std::size_t promoted_position = (MAX_KEYS + 1) / 2;
        const Key promoted_key = temporary_keys[promoted_position];

        const std::size_t left_key_count = promoted_position;
        const std::size_t right_key_count =
            MAX_KEYS - promoted_position;

        const std::uint32_t new_right_id =
            allocateNode(false, current.header.parent);
        Node &new_right = node(new_right_id);

        current.header.count =
            static_cast<std::uint16_t>(left_key_count);
        for (std::size_t i = 0; i < left_key_count; ++i) {
            current.data.internal.keys[i] = temporary_keys[i];
        }
        for (std::size_t i = 0; i <= left_key_count; ++i) {
            current.data.internal.children[i] = temporary_children[i];
        }

        new_right.header.count =
            static_cast<std::uint16_t>(right_key_count);
        for (std::size_t i = 0; i < right_key_count; ++i) {
            new_right.data.internal.keys[i] =
                temporary_keys[promoted_position + 1 + i];
        }
        for (std::size_t i = 0; i <= right_key_count; ++i) {
            const std::uint32_t child_id =
                temporary_children[promoted_position + 1 + i];
            new_right.data.internal.children[i] = child_id;

            Node &child = node(child_id);
            child.header.parent = new_right_id;
            file_.markDirty(child_id);
        }

        file_.markDirty(node_id);
        file_.markDirty(new_right_id);

        insertIntoParent(node_id, promoted_key, new_right_id);
    }

    void removeChildFromParent(std::uint32_t parent_id,
                               std::size_t key_position) {
        Node &parent = node(parent_id);
        const std::size_t old_count = parent.header.count;

        for (std::size_t i = key_position;
             i + 1 < old_count;
             ++i) {
            parent.data.internal.keys[i] =
                parent.data.internal.keys[i + 1];
        }

        for (std::size_t i = key_position + 1;
             i < old_count;
             ++i) {
            parent.data.internal.children[i] =
                parent.data.internal.children[i + 1];
        }

        --parent.header.count;
        file_.markDirty(parent_id);
    }

    void rebalanceLeaf(std::uint32_t leaf_id) {
        Node &leaf = node(leaf_id);
        const std::uint32_t parent_id = leaf.header.parent;
        Node &parent = node(parent_id);
        const std::size_t position = childPosition(parent, leaf_id);

        if (position > 0) {
            const std::uint32_t left_id =
                parent.data.internal.children[position - 1];
            Node &left = node(left_id);

            if (left.header.count > MIN_KEYS) {
                for (std::size_t i = leaf.header.count; i > 0; --i) {
                    leaf.data.leaf.keys[i] =
                        leaf.data.leaf.keys[i - 1];
                }

                leaf.data.leaf.keys[0] =
                    left.data.leaf.keys[left.header.count - 1];
                --left.header.count;
                ++leaf.header.count;

                parent.data.internal.keys[position - 1] =
                    leaf.data.leaf.keys[0];

                file_.markDirty(left_id);
                file_.markDirty(leaf_id);
                file_.markDirty(parent_id);
                return;
            }
        }

        if (position < parent.header.count) {
            const std::uint32_t right_id =
                parent.data.internal.children[position + 1];
            Node &right = node(right_id);

            if (right.header.count > MIN_KEYS) {
                leaf.data.leaf.keys[leaf.header.count] =
                    right.data.leaf.keys[0];
                ++leaf.header.count;

                for (std::size_t i = 0;
                     i + 1 < right.header.count;
                     ++i) {
                    right.data.leaf.keys[i] =
                        right.data.leaf.keys[i + 1];
                }
                --right.header.count;

                parent.data.internal.keys[position] =
                    right.data.leaf.keys[0];

                file_.markDirty(leaf_id);
                file_.markDirty(right_id);
                file_.markDirty(parent_id);
                return;
            }
        }

        if (position > 0) {
            const std::uint32_t left_id =
                parent.data.internal.children[position - 1];
            Node &left = node(left_id);

            const std::size_t left_count = left.header.count;
            for (std::size_t i = 0; i < leaf.header.count; ++i) {
                left.data.leaf.keys[left_count + i] =
                    leaf.data.leaf.keys[i];
            }
            left.header.count =
                static_cast<std::uint16_t>(left_count +
                                           leaf.header.count);
            left.header.next = leaf.header.next;

            if (leaf.header.next != 0) {
                Node &next_leaf = node(leaf.header.next);
                next_leaf.header.previous = left_id;
                file_.markDirty(next_leaf.header.self);
            }

            file_.markDirty(left_id);
            removeChildFromParent(parent_id, position - 1);
            releaseNode(leaf_id);
            rebalanceInternal(parent_id);
            return;
        }

        const std::uint32_t right_id =
            parent.data.internal.children[position + 1];
        Node &right = node(right_id);

        const std::size_t leaf_count = leaf.header.count;
        for (std::size_t i = 0; i < right.header.count; ++i) {
            leaf.data.leaf.keys[leaf_count + i] =
                right.data.leaf.keys[i];
        }
        leaf.header.count =
            static_cast<std::uint16_t>(leaf_count +
                                       right.header.count);
        leaf.header.next = right.header.next;

        if (right.header.next != 0) {
            Node &next_leaf = node(right.header.next);
            next_leaf.header.previous = leaf_id;
            file_.markDirty(next_leaf.header.self);
        }

        file_.markDirty(leaf_id);
        removeChildFromParent(parent_id, position);
        releaseNode(right_id);
        rebalanceInternal(parent_id);
    }

    void rebalanceInternal(std::uint32_t node_id) {
        Node &current = node(node_id);

        if (node_id == file_.metadata().root) {
            if (current.header.count == 0) {
                const std::uint32_t new_root_id =
                    current.data.internal.children[0];
                Node &new_root = node(new_root_id);
                new_root.header.parent = 0;

                file_.metadata().root = new_root_id;
                file_.markDirty(new_root_id);
                releaseNode(node_id);
            }
            return;
        }

        if (current.header.count >= MIN_KEYS) {
            return;
        }

        const std::uint32_t parent_id = current.header.parent;
        Node &parent = node(parent_id);
        const std::size_t position =
            childPosition(parent, node_id);

        if (position > 0) {
            const std::uint32_t left_id =
                parent.data.internal.children[position - 1];
            Node &left = node(left_id);

            if (left.header.count > MIN_KEYS) {
                const std::size_t current_count =
                    current.header.count;

                for (std::size_t i = current_count; i > 0; --i) {
                    current.data.internal.keys[i] =
                        current.data.internal.keys[i - 1];
                }
                for (std::size_t i = current_count + 1;
                     i > 0;
                     --i) {
                    current.data.internal.children[i] =
                        current.data.internal.children[i - 1];
                }

                current.data.internal.keys[0] =
                    parent.data.internal.keys[position - 1];

                const std::uint32_t moved_child =
                    left.data.internal.children[left.header.count];
                current.data.internal.children[0] = moved_child;

                parent.data.internal.keys[position - 1] =
                    left.data.internal.keys[left.header.count - 1];

                --left.header.count;
                ++current.header.count;

                Node &child = node(moved_child);
                child.header.parent = node_id;

                file_.markDirty(left_id);
                file_.markDirty(node_id);
                file_.markDirty(parent_id);
                file_.markDirty(moved_child);
                return;
            }
        }

        if (position < parent.header.count) {
            const std::uint32_t right_id =
                parent.data.internal.children[position + 1];
            Node &right = node(right_id);

            if (right.header.count > MIN_KEYS) {
                const std::size_t current_count =
                    current.header.count;
                const std::size_t right_count =
                    right.header.count;

                current.data.internal.keys[current_count] =
                    parent.data.internal.keys[position];

                const std::uint32_t moved_child =
                    right.data.internal.children[0];
                current.data.internal.children[current_count + 1] =
                    moved_child;

                parent.data.internal.keys[position] =
                    right.data.internal.keys[0];

                for (std::size_t i = 0;
                     i + 1 < right_count;
                     ++i) {
                    right.data.internal.keys[i] =
                        right.data.internal.keys[i + 1];
                }
                for (std::size_t i = 0; i < right_count; ++i) {
                    right.data.internal.children[i] =
                        right.data.internal.children[i + 1];
                }

                ++current.header.count;
                --right.header.count;

                Node &child = node(moved_child);
                child.header.parent = node_id;

                file_.markDirty(node_id);
                file_.markDirty(right_id);
                file_.markDirty(parent_id);
                file_.markDirty(moved_child);
                return;
            }
        }

        if (position > 0) {
            const std::uint32_t left_id =
                parent.data.internal.children[position - 1];
            Node &left = node(left_id);

            const std::size_t left_count = left.header.count;
            const std::size_t current_count = current.header.count;

            left.data.internal.keys[left_count] =
                parent.data.internal.keys[position - 1];

            for (std::size_t i = 0; i < current_count; ++i) {
                left.data.internal.keys[left_count + 1 + i] =
                    current.data.internal.keys[i];
            }

            for (std::size_t i = 0; i <= current_count; ++i) {
                const std::uint32_t child_id =
                    current.data.internal.children[i];
                left.data.internal.children[left_count + 1 + i] =
                    child_id;

                Node &child = node(child_id);
                child.header.parent = left_id;
                file_.markDirty(child_id);
            }

            left.header.count =
                static_cast<std::uint16_t>(left_count +
                                           current_count + 1);

            file_.markDirty(left_id);
            removeChildFromParent(parent_id, position - 1);
            releaseNode(node_id);
            rebalanceInternal(parent_id);
            return;
        }

        const std::uint32_t right_id =
            parent.data.internal.children[position + 1];
        Node &right = node(right_id);

        const std::size_t current_count = current.header.count;
        const std::size_t right_count = right.header.count;

        current.data.internal.keys[current_count] =
            parent.data.internal.keys[position];

        for (std::size_t i = 0; i < right_count; ++i) {
            current.data.internal.keys[current_count + 1 + i] =
                right.data.internal.keys[i];
        }

        for (std::size_t i = 0; i <= right_count; ++i) {
            const std::uint32_t child_id =
                right.data.internal.children[i];
            current.data.internal.children[current_count + 1 + i] =
                child_id;

            Node &child = node(child_id);
            child.header.parent = node_id;
            file_.markDirty(child_id);
        }

        current.header.count =
            static_cast<std::uint16_t>(current_count +
                                       right_count + 1);

        file_.markDirty(node_id);
        removeChildFromParent(parent_id, position);
        releaseNode(right_id);
        rebalanceInternal(parent_id);
    }
};

}  // namespace

int main() {
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    try {
        BPlusTree tree("bpt_storage.dat");

        int command_count = 0;
        if (!(std::cin >> command_count)) {
            return 0;
        }

        for (int i = 0; i < command_count; ++i) {
            std::string command;
            std::string index;
            std::cin >> command >> index;

            if (command == "insert") {
                std::int32_t value = 0;
                std::cin >> value;
                tree.insert(index, value);
            } else if (command == "delete") {
                std::int32_t value = 0;
                std::cin >> value;
                tree.erase(index, value);
            } else if (command == "find") {
                tree.find(index, std::cout);
            } else {
                throw std::runtime_error("Unknown command");
            }
        }

        tree.flush();
    } catch (const std::exception &error) {
        std::cerr << error.what() << '\n';
        return 1;
    }

    return 0;
}
