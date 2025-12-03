add_library(breakconstantgeps SHARED BreakConstantGEPs.cpp)
target_link_libraries(breakconstantgeps LLVM)
target_include_directories(breakconstantgeps PUBLIC ../include/)