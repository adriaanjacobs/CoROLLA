#pragma once

#include <llvm/Pass.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Instructions.h>

struct CallSiteAnalysisResult {
    struct CallSiteInfo {
        llvm::Function* func;
        llvm::DenseSet<llvm::CallBase*> directCallSites;
        llvm::DenseSet<llvm::Use*> opaqueUses;

        CallSiteInfo(llvm::Function* func) : 
            func{func} 
        {}
        bool isOnlyDirectlyCalled () const;
        bool noUsesFound() const;
    };

    const CallSiteInfo& getCallSiteInfo(llvm::Function* function) const;
    void forgetCallSiteInfo(llvm::Function* function);

    // warning: currently ignores direct calls from external code (publically linked functions)
    // warning: also ignores 'byval' attributes on arguments. Callers should manually check & handle this if relevant
    bool getIncomingValuesForArgument(llvm::Argument* argument, llvm::DenseSet<llvm::Value*>& incomingVals) const;

    CallSiteAnalysisResult(llvm::Module&, llvm::ModuleAnalysisManager&);

private:
    llvm::Module& module;
    llvm::ModuleAnalysisManager& MAM;
    mutable llvm::DenseMap<llvm::Function*, CallSiteInfo> cachedCallSiteInfo;
    void collectCallSiteInfo(llvm::Value* function, llvm::DenseSet<llvm::CallBase*>& callSites, llvm::DenseSet<llvm::Use*>& opaqueUses) const;
};

class CallSiteAnalysis : public llvm::AnalysisInfoMixin<CallSiteAnalysis> {
public:

    explicit CallSiteAnalysis() = default;
    ~CallSiteAnalysis() = default;
    // Provide a unique key, i.e., memory address to be used by the LLVM's pass
    // infrastructure.
    static llvm::AnalysisKey Key;
    friend llvm::AnalysisInfoMixin<CallSiteAnalysis>;

    // Specify the result type of this analysis pass.
    using Result = CallSiteAnalysisResult;

    // Analyze the bitcode/IR in the given LLVM module.
    Result run(llvm::Module &M, [[maybe_unused]] llvm::ModuleAnalysisManager &MAM);
};
