project(pointerdetection)

cmake_minimum_required(VERSION 3.4.3)

#===============================================================================
# 3. ADD THE TARGET
#===============================================================================
add_library(ptrdetectionpass SHARED pointerdetector.cpp)
target_compile_options(ptrdetectionpass PRIVATE ${COMMON_FLAGS})

# Allow undefined symbols in shared objects on Darwin (this is the default
# behaviour on Linux)
target_link_libraries(ptrdetectionpass svfpass)