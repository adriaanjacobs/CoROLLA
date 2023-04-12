project(pointerdetection)

cmake_minimum_required(VERSION 3.4.3)

#===============================================================================
# 3. ADD THE TARGET
#===============================================================================
add_library(ptrdetectionpass SHARED pointerdetector.cpp sillyperlanalysis.cpp)
target_compile_options(ptrdetectionpass PRIVATE ${COMMON_FLAGS})
target_link_libraries(ptrdetectionpass svfpass)
