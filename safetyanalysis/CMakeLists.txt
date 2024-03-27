
add_library(safetyanalysis SHARED safetyanalysis.cpp allocationbounds.cpp boundschecker.cpp)
target_link_libraries(safetyanalysis reachability)

add_executable(mpk_instrument passrunner.cpp)
target_link_libraries(mpk_instrument safetyanalysis)
