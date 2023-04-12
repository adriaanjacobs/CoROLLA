project(safetyanalysis)

cmake_minimum_required(VERSION 3.4.3)

#===============================================================================
# 3. ADD THE TARGET
#===============================================================================
add_library(IRPass SHARED pass.cpp allocationwrappers.cpp offsetfinder.cpp boundschecker.cpp LTOplugin_boilerplate.cpp)
target_compile_options(IRPass PRIVATE ${COMMON_FLAGS})
target_link_libraries(IRPass reachability)

add_executable(mpk_instrument passrunner.cpp)
target_compile_options(mpk_instrument PRIVATE ${COMMON_FLAGS})
target_link_libraries(mpk_instrument IRPass)
