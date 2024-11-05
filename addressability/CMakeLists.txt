add_library(addressability SHARED 
    addressability.cpp
    pointer_escapes.cpp
)
target_link_libraries(addressability util safetyanalysis callsiteanalysis)
