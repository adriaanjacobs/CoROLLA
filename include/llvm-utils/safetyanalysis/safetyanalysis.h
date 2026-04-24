#pragma once

#include <llvm-utils/util.h>

#include <llvm/IR/Verifier.h>
#include <llvm/Analysis/MemoryBuiltins.h>

#include <optional>

// Simple wrapper around LLVM's builtin ObjectSizeOffsetVisitor
class OSOVAnalysis : public llvm::AnalysisInfoMixin<OSOVAnalysis> {
public:
    explicit OSOVAnalysis() = default;
    ~OSOVAnalysis() = default;
    // Provide a unique key, i.e., memory address to be used by the LLVM's pass
    // infrastructure.
    static llvm::AnalysisKey Key;
    friend llvm::AnalysisInfoMixin<OSOVAnalysis>;

    // Specify the result type of this analysis pass.
    class Result {
        [[maybe_unused]]
        llvm::Function& F;
        [[maybe_unused]]
        llvm::FunctionAnalysisManager& FAM;
        const llvm::DataLayout& DL;
        llvm::ObjectSizeOffsetVisitor OSOV;
        llvm::DenseSet<llvm::Use*> unsafeUses;

        bool computeIsInBounds(llvm::Use*);

    public:
        Result(llvm::Function& F, llvm::FunctionAnalysisManager& FAM);

        bool isInBounds(llvm::Use*);
    };

    // Analyze the bitcode/IR in the given LLVM module.
    Result run(llvm::Function& F, [[maybe_unused]] llvm::FunctionAnalysisManager& FAM);
};

//===----------------------------------------------------------------------===//
/// This class implements an LLVM module analysis pass.
///
class IsInBoundsAnalysis : public llvm::AnalysisInfoMixin<IsInBoundsAnalysis> {
public:

    struct BoundsChecker {
        using enum DIRECTION;
        BoundsChecker(llvm::Module& module, [[maybe_unused]] llvm::ModuleAnalysisManager &MAM) : 
            module{module}, MAM{MAM}
        {}
        
        // "is this dangerously out of bounds?" / "may this access out-of-bounds memory without crashing?"
        // because provably unmapped memory (like NULL) is still considered in bounds
        bool isInBounds(llvm::Value* offsetPtr, llvm::APInt offset = llvm::APInt{64,0});
        bool isInBounds(llvm::Use* offsetPtrUse, llvm::APInt offset = llvm::APInt{64,0});

        // does not update cache, does not update bailstats. Useful for non-isinbounds range queries
        bool isInRange_nonCached(llvm::Value* offsetPtr, llvm::APInt offset, const std::function<std::optional<bool>(llvm::Value*, llvm::APInt, DIRECTION)>& isInRange);

        void printBailStats();
    private:
        struct IsInBoundsResult {
            bool inBounds;
            llvm::StringRef explanation;

            static IsInBoundsResult False(llvm::StringRef expl) {
                return IsInBoundsResult{false, expl};
            }

            static IsInBoundsResult True() {
                return IsInBoundsResult{true, ""};
            }
        };
        template<DIRECTION DIR>
        IsInBoundsResult isInBounds_internal(llvm::Value* offsetPtr, llvm::APInt storeSize, const std::function<std::optional<bool>(llvm::Value*, llvm::APInt, DIRECTION)>& isInRange, bool checkTheCache = true);
        std::optional<IsInBoundsResult> isInCache(llvm::Value* offsetPtr, llvm::APInt offset) const;

        llvm::SmallVector<llvm::CallBase*> callStack;
        llvm::DenseMap<llvm::Value*, llvm::DenseMap<llvm::APInt, std::optional<IsInBoundsResult>>> boundsCache;
        llvm::DenseMap<llvm::StringRef, size_t> bailStats;
        llvm::Module& module;
        llvm::ModuleAnalysisManager& MAM;
    };

    explicit IsInBoundsAnalysis() = default;
    ~IsInBoundsAnalysis() = default;
    // Provide a unique key, i.e., memory address to be used by the LLVM's pass
    // infrastructure.
    static llvm::AnalysisKey Key;
    friend llvm::AnalysisInfoMixin<IsInBoundsAnalysis>;

    // Specify the result type of this analysis pass.
    using Result = BoundsChecker;

    // Analyze the bitcode/IR in the given LLVM module.
    Result run(llvm::Module& module, [[maybe_unused]] llvm::ModuleAnalysisManager& MAM);

    static void addPreparationPasses(llvm::ModulePassManager& MPM);
    static void addCleanupPasses(llvm::ModulePassManager& MPM);

public:
    template<typename PassT, typename VerifierT = llvm::VerifierPass>
    static void addPassesAround(llvm::ModulePassManager& MPM) {
        addPreparationPasses(MPM);
        MPM.addPass(PassT{});
        MPM.addPass(VerifierT{});
        addCleanupPasses(MPM);
    }
};

using BoundsChecker = IsInBoundsAnalysis::BoundsChecker;


//===----------------------------------------------------------------------===//
/// This class implements an LLVM module analysis pass.
///
class UnsafeAccessFinderAnalysis : public llvm::AnalysisInfoMixin<UnsafeAccessFinderAnalysis> {
public:

    struct UnsafeAccessInfo {
        explicit UnsafeAccessInfo(llvm::Module& module, llvm::ModuleAnalysisManager& MAM, bool onlyStores);

        llvm::Module& module;
        llvm::ModuleAnalysisManager& MAM;
        const bool onlyStores;

        llvm::DenseSet<llvm::Instruction *> unsafeAccesses;
    };
    
    explicit UnsafeAccessFinderAnalysis() = default;
    ~UnsafeAccessFinderAnalysis() = default;
    // Provide a unique key, i.e., memory address to be used by the LLVM's pass
    // infrastructure.
    static llvm::AnalysisKey Key;
    friend llvm::AnalysisInfoMixin<UnsafeAccessFinderAnalysis>;

    // Specify the result type of this analysis pass.
    using Result = AnalysisResultBuilder<UnsafeAccessInfo>;

    // Analyze the bitcode/IR in the given LLVM module.
    Result run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
        return Result{M, MAM};
    }
};

using UnsafeAccessInfo = UnsafeAccessFinderAnalysis::UnsafeAccessInfo;

//===----------------------------------------------------------------------===//
/// This class implements an LLVM module transformation pass.
///
class AllocWrapperAlwaysInlineMarkerPass : public llvm::PassInfoMixin<AllocWrapperAlwaysInlineMarkerPass> {
public:
    explicit AllocWrapperAlwaysInlineMarkerPass() = default;
    ~AllocWrapperAlwaysInlineMarkerPass() = default;

    // Transform the bitcode/IR in the given LLVM module.
    llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM);
};

//===----------------------------------------------------------------------===//
/// This class implements an LLVM module transformation pass.
///
class MemAccessInstrumentator : public llvm::PassInfoMixin<MemAccessInstrumentator> {
public:
    explicit MemAccessInstrumentator() = default;
    ~MemAccessInstrumentator() = default;

    // Transform the bitcode/IR in the given LLVM module.
    llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM);

    static bool isRequired() { return true; }
    static void registerAnalyses(llvm::ModuleAnalysisManager& MAM);
};
