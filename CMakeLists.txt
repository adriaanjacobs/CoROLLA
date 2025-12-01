cmake_minimum_required(VERSION 3.5)

project(llvm-utils)

# exclude all targets here from default compilation. 
# Build only those that a parent user depends on
set_directory_properties(PROPERTIES EXCLUDE_FROM_ALL YES)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

find_package(LLVM 15 REQUIRED CONFIG)
message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
find_package(Clang REQUIRED)
message(STATUS "Found Clang ${Clang_PACKAGE_VERSION}")
message(STATUS "Using ClangConfig.cmake in: ${Clang_DIR}")
include_directories(${LLVM_INCLUDE_DIRS})

set(clang_libs clang-cpp)

include_directories(include/)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_C_STANDARD 17)

add_compile_options(-Wall -Wextra -Werror=return-type -Wno-c99-designator -Wimplicit-fallthrough -Wno-comment  -Wno-unused-parameter -Wno-unused-variable -Wno-unused-but-set-variable)
add_compile_options(-ggdb -fPIC -fno-rtti)
add_compile_options(-O2)

add_library(util SHARED util.cpp)
target_link_libraries(util breakconstantgeps)
# everyone depends on this, so everyone gets the include path
target_include_directories(util PUBLIC include/)

add_subdirectory(breakconstantgeps)
add_subdirectory(compileOTF)
add_subdirectory(instrpointoptimization)
add_subdirectory(callsiteanalysis)
add_subdirectory(pointerdetection)
add_subdirectory(reachability)
add_subdirectory(safetyanalysis)
add_subdirectory(addressability)

# Convenience library to link in by users of llvm-utils
add_library(llvmutils INTERFACE)
target_link_libraries(llvmutils INTERFACE
    util
    breakconstantgeps
    callsiteanalysis
    instrpointoptimization
    ptrdetectionpass
    reachability
    safetyanalysis
    addressability
)
target_include_directories(llvmutils INTERFACE include/)
