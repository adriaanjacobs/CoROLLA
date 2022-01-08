project(safefunctioncloner)

cmake_minimum_required(VERSION 3.4.3)

#===============================================================================
# 3. ADD THE TARGET
#===============================================================================
add_library(safefunctionclonepass SHARED safefunctioncloner.cpp)
target_compile_options(safefunctionclonepass PRIVATE ${COMMON_FLAGS})

# Allow undefined symbols in shared objects on Darwin (this is the default
# behaviour on Linux)
target_link_libraries(safefunctionclonepass ptrdetectionpass IRPass wrapgepspass ${svf_libs} ${llvm_libs})