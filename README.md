# CoROLLA: <ins>Co</ins>llection of <ins>R</ins>eusable <ins>O</ins>ut-of-tree <ins>LL</ins>VM <ins>A</ins>uxiliaries

Suite of LLVM analyses and utilities, mostly for academic purposes. Many implement aggressive but sound versions of popular optimizations. Some examples:
* [`safetyanalysis/`](/safetyanalysis/): domination pruning & interprocedural pointer safety analysis
* [`instrpointoptimization/`](/instrpointoptimization): interproceduraloop hoisting 
* [`callsiteanalysis/`](/callsiteanalysis/): sound callsite analysis
* [`addressability/`](/addressability/): sound interprocedural escape analysis
* [`reachability/`](/reachability/): instruction-granular intraprocedural reachability analysis

Among others. 

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

Note that we mostly use this code with LLVM 15. Only the code in `safetyanalysis` still has a hard dependency on non-opaque pointers, everything else can likely be made to compile with other LLVM versions fairly painlessly. 

## Usage
The easiest way to use these utils is by linking to the `corolla` interface cmake target. You can also link to individual components, and only the components you use will be built (to facilitate development using other LLVM verions). 

Note that this code expects to link to the shared `libLLVM.so` megalib. If your usage code links to LLVM statically in any way, you will get "command-line option registered more than once" errors. Just link everything to `libLLVM.so` instead. 
