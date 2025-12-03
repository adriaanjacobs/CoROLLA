add_library(instrpointoptimization SHARED 
    domination_pruning.cpp
    loopoptimizations.cpp
)
target_link_libraries(instrpointoptimization reachability)
