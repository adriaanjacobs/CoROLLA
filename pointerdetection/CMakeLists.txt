add_library(ptrdetectionpass SHARED pointerdetector.cpp sillyperlanalysis.cpp pointerqueries.cpp)
# also technically depends on reachability, but want to avoid circular dependency here
#   should probably restructure the code a bit to avoid this
target_link_libraries(ptrdetectionpass util callsiteanalysis)
