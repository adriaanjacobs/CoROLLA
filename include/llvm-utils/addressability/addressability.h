#pragma once

#include <llvm-utils/safetyanalysis/safetyanalysis.h>
#include <llvm-utils/callsiteanalysis/callsiteanalysis.h>

// interprocedural def-use walk to see what instructions this allocSites flows to
//  mostly used to prune out safe stack allocations
bool ptrMayReachUnsafeAccesses(llvm::Value* ptr, const UnsafeAccessInfo& unsafeAccessInfo, const CallSiteAnalysisResult& callSiteAnalysis);

