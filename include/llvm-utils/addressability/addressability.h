#pragma once

#include <llvm-utils/safetyanalysis/safetyanalysis.h>
#include <llvm-utils/callsiteanalysis/callsiteanalysis.h>

// interprocedural def-use walk to see what instructions this allocSites flows to
//  mostly used to prune out safe stack allocations
bool ptrMayReachUnsafeAccesses(llvm::Value* ptr, const UnsafeAccessInfo& unsafeAccessInfo, const CallSiteAnalysisResult& callSiteAnalysis);

// internalize a bunch of functions that may be called indirectly/from external code
//  according to CallSiteAnalysis
// returns a mapping between the inserted wrapper function and the wrapped ("internalized") function
// the "internalized" functions are suitable for invasive transformations like signature changes etc.
llvm::DenseMap<llvm::Function*, llvm::Function*> wrapAddressTakenFuncs(llvm::Module& module, llvm::ModuleAnalysisManager& MAM);
