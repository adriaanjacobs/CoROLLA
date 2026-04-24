#pragma once

#include <llvm-utils/safetyanalysis/safetyanalysis.h>
#include <llvm-utils/callsiteanalysis/callsiteanalysis.h>
#include <llvm-utils/pointerdetection/pointerdetection.h>

// interprocedural def-use walk to see what instructions this allocSites flows to
//  mostly used to prune out safe stack allocations
bool ptrMayReachUnsafeAccesses(llvm::Value* ptr, const UnsafeAccessInfo& unsafeAccessInfo, const CallSiteAnalysisResult& callSiteAnalysis);

// internalize a bunch of functions that may be called indirectly/from external code
//  according to CallSiteAnalysis
// returns a mapping between the inserted wrapper function and the wrapped ("internalized") function
// the "internalized" functions are suitable for invasive transformations like signature changes etc.
llvm::DenseMap<llvm::Function*, llvm::Function*> wrapAddressTakenFuncs(llvm::Module& module, llvm::ModuleAnalysisManager& MAM);

struct PointerDetector;
struct BasePtrInfo;

void collectIntraProceduralPtrEscapes(llvm::Value* ptr, llvm::DenseSet<llvm::Use*>& ptrEscapes, const PointerDetector* pointerInfo = nullptr);

struct BasePtrTracker {
    struct BasePtrTrackerInfo {
        llvm::Value* baseTracker;
        std::optional<bool> isModified;
    };
    std::function<BasePtrInfo(llvm::Value*)> findBasePtr;
    std::function<llvm::Value*(llvm::Value*)> insertAtBase;
    llvm::DenseMap<llvm::Value*, BasePtrTrackerInfo> cachedTrackers;

    BasePtrTracker(std::function<BasePtrInfo(llvm::Value*)> find_base_ptr, std::function<llvm::Value*(llvm::Value*)> insertAtBase = [] (llvm::Value* ptr) { return ptr; });

    // propagates intraprocedural base pointers (arguments, loads, calls, ...) through merges (select, phi) 
    // and returns a variable representing the value of the base pointer when `ptr` is live
    //  or the result of a custom computation if `insertAtBase` was specified
    BasePtrTrackerInfo trackBasePtr(llvm::Value* ptr);
};

