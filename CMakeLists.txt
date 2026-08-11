cmake_minimum_required(VERSION 3.16)

project(problem_016_file_storage_bpt LANGUAGES CXX)

add_executable(code main.cpp)

target_compile_features(code PRIVATE cxx_std_17)

if(CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
    target_compile_options(code PRIVATE -O2 -Wall -Wextra -Wpedantic)
endif()
