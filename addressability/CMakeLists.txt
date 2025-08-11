add_library(addressability SHARED 
    addressability.cpp
    pointer_escapes.cpp
    wrap_addresstaken_funcs.cpp
)
target_link_libraries(addressability util safetyanalysis callsiteanalysis)
