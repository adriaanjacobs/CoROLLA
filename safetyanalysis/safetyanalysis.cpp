#include <llvm-utils/safetyanalysis/safetyanalysis.h>

#include <llvm-utils/util.h>
#include <llvm-utils/safetyanalysis/allocationbounds.h>
#include <llvm-utils/pointerdetection/pointerdetection.h>
#include <llvm-utils/reachability/reachingdefinitions.h>
#include <llvm-utils/breakconstantgeps/BreakConstantGEPs.h>
#include <llvm-utils/callsiteanalysis/callsiteanalysis.h>
#include <llvm-utils/instrpointoptimization/dominationpruning.h>

#include <llvm/IR/IntrinsicsX86.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Transforms/Scalar/DCE.h>
#include <llvm/Transforms/Scalar/SimplifyCFG.h>
#include <llvm/Transforms/IPO/AlwaysInliner.h>
#include <llvm/Transforms/Utils/Mem2Reg.h>
#include <llvm/Transforms/IPO/CalledValuePropagation.h>
#include <llvm/Transforms/IPO/FunctionAttrs.h>
#include <llvm/Transforms/IPO/InferFunctionAttrs.h>
#include <llvm/Transforms/IPO/SyntheticCountsPropagation.h>
#include <llvm/Transforms/Scalar/LICM.h>
#include <llvm/Transforms/Scalar/LoopDeletion.h>
#include <llvm/Transforms/Scalar/LICM.h>
#include <llvm/Transforms/Scalar/IndVarSimplify.h>
#include <llvm/Transforms/Scalar/LoopFlatten.h>
#include <llvm/Transforms/Scalar/SimpleLoopUnswitch.h>
#include <llvm/Transforms/Scalar/LoopRotation.h>

#include <experimental/array>
#include <optional>
#include <cstdint>

UnsafeAccessFinderAnalysis::UnsafeAccessInfo::UnsafeAccessInfo(llvm::Module& module, llvm::ModuleAnalysisManager& MAM, bool onlyStores) :
    module{module}, MAM{MAM}, onlyStores{onlyStores}
{
    srand(time(NULL));

    auto& FAM = getFAM(module, MAM);

    llvm::DenseMap<llvm::Value*, llvm::DenseMap<size_t, llvm::DenseSet<llvm::Instruction*>>> ptrToTypeSizeToInstructions;    
    const llvm::DataLayout& dataLayout = module.getDataLayout();
    auto& sillyPerls = MAM.getResult<SillyPerlAnalysis>(module);
    auto& pointerDetector = MAM.getResult<PointerDetectionAnalysis>(module);
    size_t totalMemAccesses = 0;
    for (auto &function : module) {
        for (auto &basicblock : function) {
            for (auto& instr : basicblock) {
                if ((!onlyStores && llvm::isa<llvm::LoadInst>(&instr)) || llvm::isa<llvm::StoreInst>(&instr)) {
                    // maybe add strippointercasts here? or my own stippointercasts?
                    auto ptr = llvm::getLoadStorePointerOperand(&instr);
                    assert(ptr);

                    auto stripOp = pointerDetector.strip_pointer_casts(ptr);
                    bool opaqueglobal = false;
                    if (!sillyPerls.contains(&instr) && llvm::isa<llvm::Constant>(stripOp)) {
                        ASSERT_ELSE_UNKOWN(isNonWrapperAllocSite(stripOp), stripOp);
                        if (auto allocBounds = findMinimumAllocBounds(stripOp, module, MAM); allocBounds.has_value() && allocBounds == std::pair{llvm::APInt{64, 0}, llvm::APInt{64, 0}}) {
                            // this is an opaque global, do not instrument
                            opaqueglobal = true;
                        }
                    }

                    auto loadStoreType = llvm::isa<llvm::LoadInst>(&instr) ? instr.getType() : llvm::dyn_cast<llvm::StoreInst>(&instr)->getValueOperand()->getType();
                    auto loadStoreSize = dataLayout.getTypeStoreSize(loadStoreType).getFixedSize();
                    if (!opaqueglobal && !sillyPerls.contains(&instr)) {
                        totalMemAccesses++;
                        ptrToTypeSizeToInstructions[ptr][loadStoreSize].insert(&instr);
                    }
                }
            }
        }
    }

    size_t numQueries = [&]  {
        size_t ret = 0;
        for (auto& [ptr, offsets] : ptrToTypeSizeToInstructions)
            ret += offsets.size();
        return ret;
    } ();

    uint64_t progress = 0;
    uint64_t unit = ptrToTypeSizeToInstructions.size()/100;
    if (unit == 0) unit = 1;

    llvm::outs() << "Running " << numQueries << " queries for " << ptrToTypeSizeToInstructions.size() << " unique pointers. Reporting every " << unit << " iterations.\n";

    auto& boundschecker = MAM.getResult<IsInBoundsAnalysis>(module);
    llvm::DenseSet<llvm::Instruction*> instrumentedInsts;
    for (const auto& [ptr, offsets] : ptrToTypeSizeToInstructions) {
        for (const auto& [loadStoreSize, insts] : offsets) {
            assert(loadStoreSize > 0 && loadStoreSize <= UINT64_MAX);
            llvm::APInt operandSize{64, loadStoreSize, false}; 
            if (!boundschecker.isInBounds(ptr, operandSize)) {
                ASSERT_ELSE_UNKOWN(!llvm::isa<llvm::Constant>(ptr), ptr);
                for (const auto& inst : insts)
                    instrumentedInsts.insert(inst);
            }

            progress++;
            if ((progress % unit) == 0) {
                llvm::outs() << 100*progress/numQueries << "%\n";
            }
        }
    }
    
    size_t intraProcedurallyPruned = totalMemAccesses - instrumentedInsts.size();
    llvm::outs() << "Out of " << totalMemAccesses << " memory accesses, we proved that " << intraProcedurallyPruned << " are safe (" << 100.0f*intraProcedurallyPruned/totalMemAccesses << "%)\n";

    size_t beforePruning = instrumentedInsts.size();
    pruneDominatedAccesses(FAM, instrumentedInsts, [&] (llvm::Value* ptr) { return pointerDetector.strip_pointer_casts(ptr); });
    llvm::outs() << "In " << beforePruning << " accesses, we were able to find " << (beforePruning - instrumentedInsts.size()) << " redundant ones (" << 100.0f*(beforePruning - instrumentedInsts.size())/beforePruning << "%).\n";

    size_t pruned = totalMemAccesses - instrumentedInsts.size();
    llvm::outs() << "In total, we pruned " << pruned << " out of " << totalMemAccesses << " memaccesses (" << (100.0f*(float)pruned/(float)totalMemAccesses) << "%)\n";

    // sanity checking
    for (auto inst : instrumentedInsts) {
        auto operand = llvm::getLoadStorePointerOperand(inst);
        auto stripOp = pointerDetector.strip_pointer_casts(operand);
        ASSERT_ELSE_UNKOWN(!llvm::isa<llvm::Constant>(stripOp), inst);
    }

    if (onlyStores)
        for (auto store : instrumentedInsts)
            assert(llvm::isa<llvm::StoreInst>(store));
    unsafeAccesses = instrumentedInsts;

    for (auto access : unsafeAccesses) 
        access->setMetadata("unsafe", llvm::MDNode::get(access->getContext(), llvm::None));
}

llvm::AnalysisKey UnsafeAccessFinderAnalysis::Key;

llvm::PreservedAnalyses MemAccessInstrumentator::run(llvm::Module &module, llvm::ModuleAnalysisManager &mam) {

    // If the results are not yet available, because no other pass requested
    // them until now, they will be computed on-the-fly.
    const auto& loadAndStores = mam.getResult<UnsafeAccessFinderAnalysis>(module).getOrCreate(false).unsafeAccesses;

    llvm::FunctionCallee wrpkru = llvm::Intrinsic::getDeclaration(&module, llvm::Intrinsic::x86_wrpkru);
    llvm::FunctionCallee rdpkru = llvm::Intrinsic::getDeclaration(&module, llvm::Intrinsic::x86_rdpkru);
    llvm::Type* int32Ty = llvm::Type::getInt32Ty(module.getContext());
    llvm::Type* int64Ty = llvm::Type::getInt64Ty(module.getContext());
    llvm::Type* voidTy = llvm::Type::getVoidTy(module.getContext());
    llvm::FunctionType* fType = llvm::FunctionType::get(voidTy, false);
    for (auto inst : loadAndStores) {
#if 0
        auto call_wrpkru = llvm::CallInst::Create(wrpkru, llvm::ArrayRef<llvm::Value*>{llvm::ConstantInt::get(int32Ty, 0)}, "", inst);
#elif 0
        auto call_rdpkru = llvm::CallInst::Create(rdpkru, "", inst);
        auto cmp = new llvm::ICmpInst(inst, llvm::ICmpInst::Predicate::ICMP_EQ, call_rdpkru, llvm::ConstantInt::get(int32Ty, 0));
        bool isStoreInst = llvm::isa<llvm::StoreInst>(inst);
        auto pointerOperand = llvm::getPointerOperand(inst);
        auto elementType = isStoreInst ? llvm::dyn_cast<llvm::StoreInst>(inst)->getPointerOperandType() : llvm::dyn_cast<llvm::LoadInst>(inst)->getPointerOperandType();
        llvm::Value* null = llvm::ConstantPointerNull::get(llvm::PointerType::getUnqual(elementType->getPointerElementType()));
        auto select = llvm::SelectInst::Create(cmp, pointerOperand, null, "", inst);
        inst->setOperand(isStoreInst, select);
#elif 0 
        auto inlineAsm = llvm::InlineAsm::get(
            fType, 
            "xor %eax, %ecx\n\txor %ecx, %eax\n\txor %eax, %ecx\n\txor %eax, %ecx\n\txor %ecx, %eax\n\txor %eax, %ecx\n\txor %eax, %ecx\n\txor %ecx, %eax\n\txor %eax, %ecx\n\txor %eax, %ecx\n\txor %ecx, %eax\n\txor %eax, %ecx\n\txor %eax, %ecx\n\txor %ecx, %eax\n\txor %eax, %ecx\n\trdtscp\n\t",
            "~{eax},~{ecx},~{edx},~{dirflag},~{fpsr},~{flags}", 
            true
        );
        auto call_inlineAsm = llvm::CallInst::Create(inlineAsm, "", inst);
        call_inlineAsm->addAttribute(llvm::AttributeList::FunctionIndex, llvm::Attribute::NoUnwind);
// #else
        // bool isStoreInst = llvm::isa<llvm::StoreInst>(inst);
        // auto pointerOperand = llvm::getPointerOperand(inst);
        // auto intptr = llvm::PtrToIntInst::Create(llvm::Instruction::CastOps::PtrToInt, pointerOperand, int64Ty, "", inst);
        // auto elementType = (isStoreInst ? llvm::dyn_cast<llvm::StoreInst>(inst)->getPointerOperandType() : llvm::dyn_cast<llvm::LoadInst>(inst)->getPointerOperandType())->getPointerElementType();
        // llvm::Value* null = llvm::ConstantPointerNull::get(llvm::PointerType::getUnqual(elementType));
        // auto hash = llvm::BinaryOperator::CreateLShr(intptr, llvm::ConstantInt::get(int64Ty, 64 - 16), "", inst);
        // auto andInst = llvm::BinaryOperator::CreateAnd(intptr, llvm::ConstantInt::get(int64Ty, UINT16_MAX), "", inst);
        // auto cmp = new llvm::ICmpInst(inst, llvm::ICmpInst::Predicate::ICMP_EQ, hash, andInst);
        // auto select = llvm::SelectInst::Create(cmp, pointerOperand, null, "", inst);
#endif
    }

    // We are lazy here and just claim that this transformation pass invalidates
    // the results of all other analysis passes.
    return llvm::PreservedAnalyses::none();
}

void MemAccessInstrumentator::registerAnalyses(llvm::ModuleAnalysisManager &MAM) {
    // Register our analyses
    MAM.registerPass([&] { return UnsafeAccessFinderAnalysis{}; });
    MAM.registerPass([&] { return CallSiteAnalysis{}; });
    MAM.registerPass([&] { return IsInBoundsAnalysis{}; });
    MAM.registerPass([&] { return PointerDetectionAnalysis{}; });
    MAM.registerPass([&] { return ReachingDefinitionsAnalysis{}; });
    MAM.registerPass([&] { return SillyPerlAnalysis{}; });
}

void IsInBoundsAnalysis::addPreparationPasses(llvm::ModulePassManager& MPM) {
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
    FPM.addPass(llvm::UnifyFunctionExitNodesPass{});
    FPM.addPass(llvm::createFunctionToLoopPassAdaptor(std::move(LPM), true, true, true));
    
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM), true));
    MPM.addPass(llvm::VerifierPass{});

    MPM.addPass(llvm::CalledValuePropagationPass{});

    MPM.addPass(BreakConstantGEPsPass{});

    MPM.addPass(llvm::SyntheticCountsPropagation{});
    // maybe we fucked up the SVF simplification
    MPM.addPass(llvm::VerifierPass{});
}

void IsInBoundsAnalysis::addCleanupPasses(llvm::ModulePassManager& MPM) {
    // this cancels out the transformations by loopsimplify
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::SimplifyCFGPass{}));
    // for any instrumentation we emitted
    MPM.addPass(llvm::AlwaysInlinerPass{});
    // removing the dead (uncalled) functions
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::DCEPass{}));
    // running mem2reg after the transformation has proven to have amazing effects 
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(llvm::PromotePass{}));
    MPM.addPass(llvm::VerifierPass{});
}
