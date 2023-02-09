#include "pass.h"

#include <llvm/Passes/PassPlugin.h>

// This part is the new way of registering your pass
extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK llvmGetPassPluginInfo() {
    return {
        LLVM_PLUGIN_API_VERSION, "SafetyAnalysisDriverPass", LLVM_VERSION_STRING,
        [](llvm::PassBuilder &PB) {
            PB.registerFullLinkTimeOptimizationLastEPCallback([](llvm::ModulePassManager &MPM, llvm::OptimizationLevel Level) {
                IsInBoundsAnalysis::addPassesAround<MemAccessInstrumentator>(MPM);
                // IsInBoundsAnalysis::addPassesAround<llvm::VerifierPass>(MPM);
            });
            PB.registerAnalysisRegistrationCallback(MemAccessInstrumentator::registerAnalyses);
        }
    };
}
