project(safetyanalysis)

cmake_minimum_required(VERSION 3.4.3)

add_library(safetyanalysis SHARED pass.cpp allocationwrappers.cpp boundschecker.cpp LTOplugin_boilerplate.cpp)
target_link_libraries(safetyanalysis reachability)

add_executable(mpk_instrument passrunner.cpp)
target_link_libraries(mpk_instrument safetyanalysis)
