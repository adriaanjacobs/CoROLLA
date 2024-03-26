#pragma once

#include <llvm-util/util.h>
#include <llvm-util/pointerdetection/pointerdetection.h>

#include <llvm/Pass.h>
#include <llvm/IR/IRPrintingPasses.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Transforms/IPO/AlwaysInliner.h>
#include <llvm/Transforms/IPO/FunctionAttrs.h>
#include <llvm/Transforms/IPO/InferFunctionAttrs.h>
#include <llvm/Transforms/IPO/SyntheticCountsPropagation.h>
#include <llvm/Transforms/IPO/CalledValuePropagation.h>
#include <llvm/Transforms/Scalar/DCE.h>
#include <llvm/Transforms/Scalar/LICM.h>
#include <llvm/Transforms/Scalar/IndVarSimplify.h>
#include <llvm/Transforms/Scalar/LoopDeletion.h>
#include <llvm/Transforms/Scalar/LoopRotation.h>
#include <llvm/Transforms/Scalar/LoopFlatten.h>
#include <llvm/Transforms/Scalar/SimpleLoopUnswitch.h>
#include <llvm/Transforms/Scalar/SimplifyCFG.h>
#include <llvm/Transforms/Utils/Mem2Reg.h>

#include <bitset>
#include <system_error>
#include <optional>
#include <functional>

#include <Util/ExtAPI.h>

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

        bool isInRange_nonCached(llvm::Value* offsetPtr, llvm::APInt offset, const std::function<std::optional<bool>(llvm::Value*, llvm::APInt, DIRECTION)>& isInRange);

        void printBailStats();

        // i don't need to differentiate between offset here FOR MY CURRENT CLONE USECASE
        llvm::DenseMap<llvm::Argument*, llvm::DenseMap<llvm::CallBase*, std::bitset<2>>> safeCallSites;
    private:
        
        template<DIRECTION DIR>
        bool isInBounds_internal(llvm::Value* offsetPtr, llvm::APInt storeSize, const std::function<std::optional<bool>(llvm::Value*, llvm::APInt, DIRECTION)>& isInRange, bool checkTheCache = true);
        std::optional<bool> isInCache(llvm::Value* offsetPtr, llvm::APInt offset) const;

        llvm::DenseMap<llvm::Value*, llvm::DenseMap<llvm::APInt, std::optional<bool>>> boundsCache;
        llvm::DenseMap<llvm::StringRef, size_t> bailStats;
        llvm::Value* mostRecentDecider = nullptr;
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

    template<typename PassT, typename VerifierT = llvm::VerifierPass>
    static void addPassesAround(llvm::ModulePassManager& MPM) {
//         MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::SimplifyCFGPass{}));
//         MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::PromotePass{}));
//         MPM.addPass(llvm::createModuleToPostOrderCGSCCPassAdaptor(llvm::ArgumentPromotionPass{}));
//         // MPM.addPass(AllocWrapperAlwaysInlineMarkerPass());
//         // MPM.addPass(llvm::AlwaysInlinerPass());
//         // MPM.addPass(llvm::VerifierPass());
//         // MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::InstCombinePass()));
//         MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::LCSSAPass()));
//         MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::LoopSimplifyPass()));
//         MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::LoopSimplifyPass{}));
//         // MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::createFunctionToLoopPassAdaptor(llvm::IndVarSimplifyPass{})));
//         // MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::createFunctionToLoopPassAdaptor(llvm::LICMPass{}
// #if MY_LLVM_VERSION >= 15
//         , true, true, true
// #endif
//         // )));
//         MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::PromotePass{}));
//         // MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::createFunctionToLoopPassAdaptor(llvm::LICMPass{}
// #if MY_LLVM_VERSION >= 15
//         , true, true, true
// #endif
//         // )));
        // print the initial module
        auto code = new std::error_code();
        auto beforestream = new llvm::raw_fd_ostream("inputmodule.debug.ll", *code);
        assert(code->value() == 0);
        MPM.addPass(llvm::PrintModulePass(*beforestream));
        // check the initial module
        MPM.addPass(llvm::VerifierPass{});
        // infer function attributes to help allocationwrapperanalysis and later points-to analyses
        MPM.addPass(llvm::InferFunctionAttrsPass{});
        MPM.addPass(llvm::createModuleToPostOrderCGSCCPassAdaptor(llvm::PostOrderFunctionAttrsPass{}));
        MPM.addPass(llvm::ReversePostOrderFunctionAttrsPass{});
        // any load/stores that LLVM can eliminate/prove safe lessen the burden for me
        MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::PromotePass{}));
        // some of the functionality in llvm (isAuxIndVar) depends on every loop having a preheader
        MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::LoopSimplifyPass{}));      
        // rotate all the loops, makes it so that loop body more frequently postdominates the preheader
        // loop rotate & LICM as much loops as possible up front
        llvm::LoopPassManager LPM;
        LPM.addPass(llvm::LoopFlattenPass{});
        LPM.addPass(llvm::IndVarSimplifyPass{});
        LPM.addPass(llvm::LoopDeletionPass{});
        LPM.addPass(llvm::LoopRotatePass{true, true});
        LPM.addPass(llvm::LICMPass{llvm::LICMOptions()});
        LPM.addPass(llvm::SimpleLoopUnswitchPass{true, true});

        llvm::FunctionPassManager FPM;
        FPM.addPass(llvm::SimplifyCFGPass{});
        FPM.addPass(llvm::LCSSAPass{});
        FPM.addPass(llvm::createFunctionToLoopPassAdaptor(std::move(LPM), true, true, true));
        
        MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM), true));
        MPM.addPass(llvm::VerifierPass{});

        MPM.addPass(llvm::CalledValuePropagationPass{});

        // SVF simplification passes
        MPM.addPass(SVFPass{});
        MPM.addPass(llvm::SyntheticCountsPropagation{});
        // maybe we fucked up the SVF simplification
        MPM.addPass(llvm::VerifierPass{});
        // our own instrumentation
        MPM.addPass(PassT{});
        // Just to be sure that none of the passes messed up the module.
        MPM.addPass(VerifierT{});
        // this cancels out the transformations by loopsimplify
        MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::SimplifyCFGPass{}));
        // for any instrumentation we emitted
        MPM.addPass(llvm::AlwaysInlinerPass{});
        // removing the dead (uncalled) functions
        MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::DCEPass{}));
        // running mem2reg after the transformation has proven to have amazing effects on my attestation instrumentation
        MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::PromotePass{}));
        MPM.addPass(VerifierT{});
        auto afterstream = new llvm::raw_fd_ostream("outputmodule.debug.ll", *code);
        assert(code->value() == 0);
        MPM.addPass(llvm::PrintModulePass(*afterstream));
    }
};

using BoundsChecker = IsInBoundsAnalysis::BoundsChecker;

//===----------------------------------------------------------------------===//
/// This class implements an LLVM module analysis pass.
///
class AllocWrapperAnalysis : public llvm::AnalysisInfoMixin<AllocWrapperAnalysis> {
public:
    explicit AllocWrapperAnalysis() = default;
    ~AllocWrapperAnalysis() = default;
    // Provide a unique key, i.e., memory address to be used by the LLVM's pass
    // infrastructure.
    static llvm::AnalysisKey Key;
    friend llvm::AnalysisInfoMixin<AllocWrapperAnalysis>;

    struct Detector {
        using enum SVF::ExtAPI::extType;
        struct AllocWrapperInfo {
            llvm::DenseSet<llvm::Value*> allocSites;
            SVF::ExtAPI::extType type = EFT_NULL;
        };

        static bool isNonWrapperAllocSite(llvm::Value* val);
        bool isAllocationSite(llvm::Value* val);
        bool isWrapperOrLibcCall(llvm::Value* val);
        llvm::StringRef getValueDescription(llvm::Value* val);

        std::optional<std::pair<llvm::APInt, llvm::APInt>> findMinimumAllocBounds(llvm::Value* allocInstr);

        Detector(llvm::Module& module, llvm::ModuleAnalysisManager& MAM);
    private:
        llvm::Module& module;
        llvm::ModuleAnalysisManager& MAM;
        PointerDetector& pointerDetector;
        llvm::DenseMap<llvm::Function*, AllocWrapperInfo> allocFuncs;

        std::pair<llvm::APInt, llvm::APInt> findMmapBounds(llvm::CallBase* callInst);
        std::pair<llvm::APInt, llvm::APInt> boundsOfReturnedPointeeType(llvm::CallBase* callInst);
        std::pair<llvm::APInt, llvm::APInt> boundsOfMallocLike(llvm::CallBase* call);
        enum struct AllocSiteStatus { NONE, NULLPTR, ALLOCSITE };
        AllocSiteStatus reducesToAllocationSite(llvm::Value* val, llvm::DenseSet<llvm::Value*>& allocSites);

        static const llvm::DenseMap<llvm::StringRef, std::function<std::pair<llvm::APInt, llvm::APInt>(Detector*,llvm::CallBase*)>> builtinLibcCallToBounds;

        std::optional<SVF::ExtAPI::extType> deriveExtFnTy(llvm::Value* val);
    public:
        const llvm::DenseMap<llvm::Function*, AllocWrapperInfo>& getAllocFuncs() { return allocFuncs; } 
        static std::optional<decltype(builtinLibcCallToBounds)::value_type::second_type> isKnownLibcAllocator(llvm::Function* func);
    };

    // Specify the result type of this analysis pass.
    using Result = Detector;

    // Analyze the bitcode/IR in the given LLVM module.
    Result run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM);
};

using AllocWrapperDetector = AllocWrapperAnalysis::Detector;

//===----------------------------------------------------------------------===//
/// This class implements an LLVM module analysis pass.
///
class UnsafeAccessFinderAnalysis : public llvm::AnalysisInfoMixin<UnsafeAccessFinderAnalysis> {
public:

    struct UnsafeAccessInfo {
        explicit UnsafeAccessInfo(llvm::Module& module, llvm::ModuleAnalysisManager& MAM, bool onlyStores);

        llvm::Module& module;
        llvm::ModuleAnalysisManager& MAM;

        llvm::DenseSet<llvm::Instruction *> unsafeAccesses;
    private: 
        void pruneDominatedAccesses(llvm::Module& module, llvm::ModuleAnalysisManager& FAM, llvm::DenseSet<llvm::Instruction*>& loadAndStores);
        static std::pair<size_t, bool> find_allocSize(const llvm::DataLayout& dataLayout, const llvm::Value* const allocInstr);
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
