#include <llvm/Pass.h>
#include <llvm/IR/PassManager.h>


//===----------------------------------------------------------------------===//
/// This class implements an LLVM module transformation pass.
///
class SafeFunctionClonerPass : public llvm::PassInfoMixin<SafeFunctionClonerPass> {
public:
    explicit SafeFunctionClonerPass() = default;
    ~SafeFunctionClonerPass() = default;

    // Transform the bitcode/IR in the given LLVM module.
    llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM);
};

