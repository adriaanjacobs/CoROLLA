project(llvm-utils)

cmake_minimum_required(VERSION 3.4.3)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

find_package(LLVM 15 REQUIRED CONFIG)
message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
find_package(Clang REQUIRED)
message(STATUS "Found Clang ${Clang_PACKAGE_VERSION}")
message(STATUS "Using ClangConfig.cmake in: ${Clang_DIR}")
include_directories(${LLVM_INCLUDE_DIRS})

llvm_map_components_to_libnames(llvm_libs Passes bitwriter core ipo irreader instcombine instrumentation target linker analysis scalaropts support transformutils)
set(clang_libs clang-cpp)

include_directories(include/)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_subdirectory(compileOTF)
add_subdirectory(instrpointoptimization)
add_subdirectory(pointerdetection)
add_subdirectory(reachability)
add_subdirectory(safefunctioncloner)
add_subdirectory(safetyanalysis)

