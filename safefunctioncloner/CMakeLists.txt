project(safefunctioncloner)

cmake_minimum_required(VERSION 3.4.3)

add_library(safefunctionclonepass SHARED safefunctioncloner.cpp)
target_link_libraries(safefunctionclonepass safetyanalysis)
