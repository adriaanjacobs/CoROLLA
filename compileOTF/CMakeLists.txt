project(compileOTF)

cmake_minimum_required(VERSION 3.4.3)

add_library(compileOTF SHARED compileOTF.cpp)
target_compile_options(compileOTF PRIVATE ${COMMON_FLAGS} ${ASAN_OPTIONS})
target_link_options(compileOTF PRIVATE ${ASAN_OPTIONS})
