#include "safefunctioncloner.h"
#include <safetyanalysis/pass.h>
#include <wrapgeps/wrapgeps.h>
#include <llvm/Transforms/Utils/Cloning.h>


llvm::PreservedAnalyses SafeFunctionClonerPass::run(llvm::Module& module, llvm::ModuleAnalysisManager& MAM) {
    auto& gepdetector = MAM.getResult<GepDetectionAnalysis>(module);
    auto boundsChecker = MAM.getCachedResult<IsInBoundsAnalysis>(module);
    assert(boundsChecker && "GepDetectionAnalysis should have filled the bounds checker!");

    if (boundsChecker->safeCallSites.empty())
        llvm::outs() << "No safe callsites found. Did the callsite analysis not run perhaps?\n";
    
    for (auto& argmap : boundsChecker->safeCallSites) {
        auto func = argmap.getFirst()->getParent();
        llvm::ValueToValueMapTy valueMapping;
        auto clonedFunc = llvm::CloneFunction(func, valueMapping);
        
        for (auto& callmap : argmap.getSecond()) {
            if (callmap.getSecond().all()) {
                callmap.getFirst()->setCalledFunction(clonedFunc);
            }
        }
    }

    return llvm::PreservedAnalyses::none();
}