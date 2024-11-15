# Collection of Reusable Out-Of-Tree LLVM Utilities

> **NOTE**: If you are a student using this code, please do not make any of the code public anywhere without my explicit permission. Otherwise, have fun. 

This repo got split off from an older megarepo some months ago. Frequent updates and breakages are expected. Entirely unstable.

## Building

> **_NOTE:_** We assume that you installed LLVM and Clang in default system folders via [apt.llvm.org](apt.llvm.org) like so
> ```bash
> wget https://apt.llvm.org/llvm.sh
> chmod +x llvm.sh
> sudo ./llvm.sh 15
> # also install clang dev
> sudo apt install libclang-15-dev
> ```

Typical cmake workflow:
```bash
mkdir build && cd build
cmake  ../ -DCMAKE_CXX_COMPILER=clang++-15 -DCMAKE_C_COMPILER=clang-15 -DLLVM_DIR=/usr/lib/llvm-15/lib/cmake/ -DClang_DIR=/usr/lib/llvm-15/lib/cmake/clang/
make -j
```

Note that this code is only ever used with LLVM 15. In particular, there is no opaque pointer support (although it's not far away). Apart from that, there's no hard constraints on which version of LLVM this code could work with, with minor modifications. 

## Usage
### Running
Some of the subdirs contain dedicated pass runners. None of them do anything directly useful, I just use them for debugging and testing. Many of the libraries can be loaded into clang/opt, sometimes also at link time for LTO, but, again, none of them will do something useful with the analysis results. 

### Linking
The easiest way to use these utils is by linking to the `llvmutils` cmake target. 

Note that this code expects to link to the shared `libLLVM.so` megalib. If your usage code links to LLVM statically in any way, you will get "command-line option registered more than once" errors. Just link everything to `libLLVM.so` instead. 
