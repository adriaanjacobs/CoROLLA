project(reachability)

add_library(reachability SHARED reachingdefinitions.cpp)
target_compile_options(reachability PRIVATE ${COMMON_FLAGS})
target_link_libraries(reachability ptrdetectionpass)
