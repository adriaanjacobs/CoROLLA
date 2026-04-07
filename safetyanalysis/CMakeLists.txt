
add_library(safetyanalysis SHARED 
    osov_analysis.cpp
    safetyanalysis.cpp 
    allocationbounds.cpp 
    boundschecker.cpp
)
target_link_libraries(safetyanalysis reachability callsiteanalysis)

add_executable(mpk_instrument passrunner.cpp)
target_link_libraries(mpk_instrument safetyanalysis)
