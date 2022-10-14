#include "pass.h"

#include <util.h>
#include <pointerdetection/pointerdetection.h>

#include <llvm/ADT/DenseSet.h>
#include <llvm/IR/CFG.h>
#include <llvm/ADT/APInt.h>
#include <llvm/ADT/ArrayRef.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/Analysis/InlineAdvisor.h>
#include <llvm/Analysis/ScalarEvolutionExpressions.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/PassManager.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/IR/ValueMap.h>
#include <llvm/ADT/STLExtras.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/Analysis/LoopAccessAnalysis.h>
#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/IR/Argument.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Metadata.h>
#include <llvm/Support/Casting.h>
#include <llvm/IR/IntrinsicsX86.h>
#include <llvm/IR/PassManagerImpl.h>
#include <llvm/IR/InlineAsm.h>

#include <experimental/array>
#include <optional>
#include <cstdint>
#include <string>


UnsafeAccessFinderAnalysis::UnsafeAccessInfo::UnsafeAccessInfo(llvm::Module& module, llvm::ModuleAnalysisManager& MAM, bool onlyStores) :
    module{module}, MAM{MAM}    
{
    srand(time(NULL));

    auto& FAM = getFAM(module, MAM);

    llvm::DenseSet<llvm::Value*> pointerOperands;
    llvm::DenseSet<llvm::Value*>  instrumentedPointerOperands;
    
    const llvm::DataLayout& dataLayout = module.getDataLayout();
    auto& sillyPerls = MAM.getResult<SillyPerlAnalysis>(module);
    for (auto &function : module) {
        for (auto &basicblock : function) {
            for (auto& instr : basicblock) {
                if ((!onlyStores && llvm::isa<llvm::LoadInst>(&instr)) || llvm::isa<llvm::StoreInst>(&instr)) {
                    // maybe add strippointercasts here? or my own stippointercasts?
                    auto operand = llvm::getLoadStorePointerOperand(&instr);
                    assert(operand);
                    if (!sillyPerls.contains(&instr))
                        pointerOperands.insert(operand);
                }
            }
        }
    }

    uint64_t progress = 0;
    uint64_t unit = pointerOperands.size()/100;
    if (unit == 0) unit = 1;

    llvm::outs() << "Size of loadAndStores: " << pointerOperands.size() << ", reporting every " << unit << " iterations.\n";

    auto& boundschecker = MAM.getResult<IsInBoundsAnalysis>(module);
    auto& allocWrappers = MAM.getResult<AllocWrapperAnalysis>(module);
    auto& pointerDetector = MAM.getResult<PointerDetectionAnalysis>(module);
    for (auto operand : pointerOperands) {
        auto loadStoreSize = dataLayout.getTypeStoreSize(operand->getType()->getPointerElementType());
        assert(loadStoreSize > 0 && loadStoreSize <= UINT64_MAX);
        llvm::APInt startOffset{64, loadStoreSize, false}; 
        if (!boundschecker.isInBounds(operand, startOffset)) {
            ASSERT_ELSE_UNKOWN(!llvm::isa<llvm::Constant>(operand), operand);
            auto stripOp = pointerDetector.strip_pointer_casts(operand);
            bool opaqueglobal = false;
            if (llvm::isa<llvm::Constant>(stripOp)) {
                assert(allocWrappers.isAllocationSite(stripOp));
                if (auto allocSize = allocWrappers.findMinimumAllocSize(stripOp); allocSize.has_value() && allocSize == 0) {
                    // this is an opaque global, do not instrument
                    opaqueglobal = true;
                }
            }
            if (!opaqueglobal)
                instrumentedPointerOperands.insert(operand);
        }

        progress++;
        if ((progress % unit) == 0) {
            llvm::outs() << 100*progress/pointerOperands.size() << "%\n";
        }
    }
    
    size_t intraProcedurallyPruned = pointerOperands.size() - instrumentedPointerOperands.size();
    llvm::outs() << "Out of " << pointerOperands.size() << " pointer operands, we proved that " << intraProcedurallyPruned << " operands are safe (" << 100.0f*intraProcedurallyPruned/pointerOperands.size() << "%)\n";

    for (auto& op : instrumentedPointerOperands) {
        assert(op != nullptr);
    }

    size_t totalMemAccesses = 0;

    llvm::DenseSet<llvm::Instruction*> loadAndStores;
    for (auto& func : module) {
        for (auto& bb : func) {
            for (auto& inst : bb) {
                if (onlyStores && !llvm::isa<llvm::StoreInst>(&inst))
                    continue;

                auto pointerOperand = llvm::getLoadStorePointerOperand(&inst);
                if (pointerOperand != nullptr)
                    totalMemAccesses++;
                if (instrumentedPointerOperands.contains(pointerOperand)) {
                    loadAndStores.insert(&inst);
                }
            }
        }
    }

    size_t pruned = totalMemAccesses - loadAndStores.size();
    llvm::outs() << "Our first analysis pruned " << pruned << " out of " << totalMemAccesses << " memaccesses (" << (100.0f*(float)pruned/(float)totalMemAccesses) << "%)\n";

    pruneDominatedAccesses(module, MAM, loadAndStores);

    pruned = totalMemAccesses - loadAndStores.size();
    llvm::outs() << "In total, we pruned " << pruned << " out of " << totalMemAccesses << " memaccesses (" << (100.0f*(float)pruned/(float)totalMemAccesses) << "%)\n";

    // sanity checking
    for (auto inst : loadAndStores) {
        auto operand = llvm::getLoadStorePointerOperand(inst);
        auto stripOp = pointerDetector.strip_pointer_casts(operand);
        ASSERT_ELSE_UNKOWN(!llvm::isa<llvm::Constant>(stripOp), inst);
    }

    if (onlyStores)
        for (auto store : loadAndStores)
            assert(llvm::isa<llvm::StoreInst>(store));
    unsafeAccesses = loadAndStores;
}

llvm::AnalysisKey UnsafeAccessFinderAnalysis::Key;

void UnsafeAccessFinderAnalysis::UnsafeAccessInfo::pruneDominatedAccesses(llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::DenseSet<llvm::Instruction*>& loadAndStores) {
    auto& FAM = getFAM(module, MAM);
    auto& pointerDetector = MAM.getResult<PointerDetectionAnalysis>(module);
    llvm::DenseMap<llvm::Value* /* operand */, llvm::SmallVector<llvm::Instruction*> /* loadAndStores */> opToUsers;
    for (auto inst : loadAndStores) {
        auto operand = pointerDetector.strip_pointer_casts(llvm::getLoadStorePointerOperand(inst));
        assert(operand);
        auto it = opToUsers.try_emplace(operand).first;
        assert(it != opToUsers.end());
        it->getSecond().push_back(inst);
    }

    llvm::DenseSet<llvm::Instruction*> toRemove;
    for (auto& opuser : opToUsers) {
        for (auto inst : opuser.getSecond()) {
            auto& domTree = FAM.getResult<llvm::DominatorTreeAnalysis>(*inst->getFunction());
            for (auto potDom : opuser.getSecond()) {
                if (potDom == inst)
                    continue;
                if (domTree.dominates(potDom, inst)) {
                    toRemove.insert(inst);
                    break;
                }
            }
        }
    }

    auto directlyDominated = toRemove.size();

    for (auto& [pointer, checks] : opToUsers) {
        // we operate on blocks here, since there may still be many checks in the same block that we haven't removed
        llvm::DenseSet<llvm::BasicBlock*> blocks;
        for (auto check : checks) 
            blocks.insert(check->getParent());

        // initial phase: collect directly-tainted blocks
        llvm::DenseSet<llvm::BasicBlock*> checkedBlocks;
        for (auto block : blocks) {
            auto function = block->getParent();
            auto& domTree = FAM.getResult<llvm::DominatorTreeAnalysis>(*function);

            llvm::SmallVector<llvm::BasicBlock*> descendants;
            domTree.getDescendants(block, descendants);
            for (auto desc : descendants) 
                checkedBlocks.insert(desc);
        }
        
        llvm::DenseSet<llvm::BasicBlock*> workingSet = checkedBlocks;
        llvm::DenseSet<llvm::BasicBlock*> prunableBlocks;
        size_t oldsize = 0;
        do {
            oldsize = workingSet.size();
            for (auto& block : workingSet) {
                const auto& preds = llvm::predecessors(block);
                bool allChecked = !preds.empty() && llvm::all_of(preds, [&] (auto pred) -> bool {
                    return workingSet.contains(pred);
                });
                if (allChecked)
                    prunableBlocks.insert(block);
            }
            workingSet.insert(prunableBlocks.begin(), prunableBlocks.end());
        } while (oldsize != workingSet.size());
        
        // final phase: convert back to checks (across functions, but yea this will not be the bottleneck)
        for (auto check : checks)
            if (prunableBlocks.contains(check->getParent()))
                toRemove.insert(check);
    }

    llvm::outs() << "In " << loadAndStores.size() << " accesses, we were able to find " << directlyDominated << " (+ " << toRemove.size()-directlyDominated << ") redundant ones (" << 100.0f*toRemove.size()/loadAndStores.size() << "%).\n";

    for (auto it = loadAndStores.begin(); it != loadAndStores.end(); ) {
        if (toRemove.contains(*it)) {
            loadAndStores.erase(it++);
        } else {
            ++it;
        }
    }
}

llvm::PreservedAnalyses MemAccessInstrumentator::run(llvm::Module &module, llvm::ModuleAnalysisManager &mam) {
    // SVF::LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(module);

    // If the results are not yet available, because no other pass requested
    // them until now, they will be computed on-the-fly.
    const auto& loadAndStores = mam.getResult<UnsafeAccessFinderAnalysis>(module)
                                            .setOnlyStores(false)
                                            .getInfo().unsafeAccesses;

    llvm::FunctionCallee wrpkru = llvm::Intrinsic::getDeclaration(&module, llvm::Intrinsic::x86_wrpkru);
    llvm::FunctionCallee rdpkru = llvm::Intrinsic::getDeclaration(&module, llvm::Intrinsic::x86_rdpkru);
    llvm::Type* int32Ty = llvm::Type::getInt32Ty(module.getContext());
    llvm::Type* int64Ty = llvm::Type::getInt64Ty(module.getContext());
    llvm::Type* voidTy = llvm::Type::getVoidTy(module.getContext());
    llvm::FunctionType* fType = llvm::FunctionType::get(voidTy, false);
    for (auto inst : loadAndStores) {

        auto call_wrpkru = llvm::CallInst::Create(wrpkru, llvm::ArrayRef<llvm::Value*>{llvm::ConstantInt::get(int32Ty, 0)}, "", inst);
#if 0
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

llvm::PreservedAnalyses AllocWrapperAlwaysInlineMarkerPass::run(llvm::Module& module, llvm::ModuleAnalysisManager &MAM) {
    auto allocDetector = MAM.getResult<AllocWrapperAnalysis>(module);

    for (const auto& [wrapper, _] : allocDetector.getAllocFuncs()) {
        wrapper->addFnAttr(llvm::Attribute::AlwaysInline);
    }

    return llvm::PreservedAnalyses::none();
}