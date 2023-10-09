#include "hoistloopmemaccesses.h"

#include "util.h"
#include <reachability/cfg_reachability.h>
#include <pointerdetection/pointerdetection.h>

#include <llvm/Transforms/Utils/ScalarEvolutionExpander.h>
#include <llvm/IR/Verifier.h>


llvm::Value* tryExpandSCEV(llvm::Module& module, llvm::ModuleAnalysisManager& MAM, const llvm::SCEV* scevVal, llvm::Type* expandedTy, llvm::Instruction* insertBefore) {
    assert(!llvm::isa<llvm::SCEVCouldNotCompute>(scevVal));
    auto& domTree = getFAM(module, MAM).getResult<llvm::DominatorTreeAnalysis>(*insertBefore->getFunction());
    auto& scev = getFAM(module, MAM).getResult<llvm::ScalarEvolutionAnalysis>(*insertBefore->getFunction());
    if (llvm::isa<llvm::SCEVAddExpr, llvm::SCEVAddRecExpr, llvm::SCEVUnknown>(scevVal)) {
        // that's okay
        llvm::SCEVExpander expander{scev, module.getDataLayout(), "MySCEVExpander"};
        auto value = expander.expandCodeFor(scevVal, expandedTy, insertBefore);

        auto isns = expander.getAllInsertedInstructions();
        auto isValid = [&] () -> bool {
            for (auto inst : isns) {
                for (auto& operandUse : inst->operands()) {
                    // do the domination check here based on BBs
                    // since we are inserting a bunch of instructions
                    if (!domTree.dominates(operandUse.get(), operandUse)) 
                        return false;
                }
            }
            return true;
        } ();
        
        if (!isValid) {
            for (auto inst : isns)
                inst->removeFromParent();
            for (auto inst : isns)
                inst->deleteValue();
            expander.clear();
            return nullptr;
        } else return value;
    } else HANDLE_UNKOWN_SCEV(scevVal);
}

void hoistLoopBoundMemAccesses(llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::DenseMap<llvm::Function*, llvm::DenseMap<llvm::Instruction*, llvm::DenseSet<InstrumentationPoint*>>>& funcToInstPoints) {
    auto& context = module.getContext();

    size_t logsInLoops = 0;
    size_t hoistedLogs = 0;
    size_t noMustExecuteLoopInvariant = 0;

    size_t cantComputeBackEdgeCount = 0;
    size_t exitValueComputed = 0;
    size_t unexpandableExitvalue = 0;
    size_t operandDependsOnIV = 0;
    size_t operandDoesNotDependOnIV = 0;
    
    for (auto& [func, instPoints] : funcToInstPoints) {
        // which instrumentation point descibes which 
        llvm::DenseMap<InstrumentationPoint*, llvm::DenseSet<llvm::Instruction*>> pointToInstructions;
        for (auto& [inst, points] : instPoints) {
            for (auto point : points) {
                assert(!pointToInstructions.count(point));
                pointToInstructions[point].insert(inst);
            }
        }

        bool change = false;
        int i = 0;

        auto& pointerDetector = MAM.getResult<PointerDetectionAnalysis>(module);
        auto& FAM = getFAM(module, MAM);
        llvm::DenseSet<llvm::Instruction*> funcTerminators;
        for (auto& bb : *func) 
            if (llvm::isa<llvm::UnreachableInst, llvm::ReturnInst>(bb.getTerminator()))
                funcTerminators.insert(bb.getTerminator());

        do {
            change = false;
            // first, we do the split-postdom preheader check, to maximally hoist non-mustExecute points
            llvm::DenseMap<llvm::Value*, llvm::DenseSet<InstrumentationPoint*>> ptrToPoints;
            for (auto& [point, _] : pointToInstructions) 
                ptrToPoints[pointerDetector.strip_pointer_casts(point->pointerOperand)].insert(point);

            auto& loopInfo = FAM.getResult<llvm::LoopAnalysis>(*func);
            auto& domTree = FAM.getResult<llvm::DominatorTreeAnalysis>(*func);
            llvm::DenseMap<llvm::Loop*, llvm::DenseSet<InstrumentationPoint*>> hoistablePoints;
            for (auto& [_, ptrPoints] : ptrToPoints) {
                llvm::DenseSet<llvm::Instruction*> exclusionSet;
                for (auto point : ptrPoints)
                    exclusionSet.insert(point->insertBefore);
                
                llvm::DenseMap<llvm::Loop*, llvm::DenseSet<InstrumentationPoint*>> loopBoundPoints;
                for (auto point : ptrPoints)
                    if (auto loop = loopInfo.getLoopFor(point->insertBefore->getParent()))
                        loopBoundPoints[loop].insert(point);
                
                for (auto& [loop, loopPoints] : loopBoundPoints) {
                    assert(!loopPoints.empty());
                    auto preheader = loop->getLoopPreheader();
                    assert(!funcTerminators.empty());
                    // are any of the function exits reachable from the preheader without logging the evidence?
                    // if not -> we can safely log the evidence from the preheader
                    auto anyTermReachable = llvm::any_of(funcTerminators, [&] (llvm::Instruction* term) -> bool {
                        return !exclusionSet.contains(&preheader->front()) && ::isPotentiallyReachable(&preheader->front(), term, exclusionSet, &domTree, &loopInfo);
                    });
                    if (!anyTermReachable) {
                        // we can safely log this evidence in the preheader
                        // only log this evidence once: erase all except 1 from the func points
                        assert(!loopPoints.empty());
                        llvm::DenseSet<llvm::Instruction*> insts;
                        for (auto point : loopPoints) {
                            for (auto inst : pointToInstructions[point])
                                insts.insert(inst);
                            pointToInstructions.erase(point);
                        }
                        for (auto inst : insts)
                            pointToInstructions[*loopPoints.begin()].insert(inst);
                        hoistablePoints[loop].insert(*loopPoints.begin());
                    }
                }
            }

            auto isHoistable = [&] (InstrumentationPoint* point) -> bool {
                auto loop = loopInfo.getLoopFor(point->insertBefore->getParent());
                assert(loop);
                if (!hoistablePoints.count(loop))
                    return false;
                return hoistablePoints[loop].contains(point);
            };

            llvm::DenseMap<InstrumentationPoint*, llvm::DenseSet<llvm::Instruction*>> pointsToInsert;
            llvm::DenseSet<InstrumentationPoint*> ivIndependentPoints;
            for (auto& [point, _] : pointToInstructions) {
                if (auto loop = loopInfo.getLoopFor(point->insertBefore->getParent())) {
                    // gcc has loops which dont seem to be in this form
                    // assert(loop->isLoopSimplifyForm());
                    logsInLoops += !i;
                    auto preheader = loop->getLoopPreheader();
                    assert(preheader);
                    assert(point->insertBefore->getParent() != preheader);
                    assert(loop->getHeader());

                    // sanity check that mustExecute points are always hoistable!!
                    const bool hoistable = isHoistable(point);
                    {
                        llvm::MustBeExecutedContextExplorer explorer = getMustBeExecutedContextExplorer(FAM, true, false);
                        bool logMustExecute = explorer.findInContextOf(point->insertBefore, preheader->getTerminator());
                        if (logMustExecute) {
                            if (!hoistable)
                                llvm::outs() << "pointerOperand: " << *point->pointerOperand << "\n";
                            ASSERT_ELSE_UNKOWN(hoistable, point->insertBefore);
                        }
                    }

                    bool changed = false;
                    if (loop->makeLoopInvariant(point->pointerOperand, changed)) {
                        assert(!changed);
                        if (hoistable) {
                            assert(domTree.dominates(point->pointerOperand, preheader->getTerminator()));
                            point->insertBefore = preheader->getTerminator();
                            hoistedLogs += !i;
                            change = true;
                        } else noMustExecuteLoopInvariant += !i;
                    } else {
                        auto& scev = FAM.getResult<llvm::ScalarEvolutionAnalysis>(*func);
                        auto operandScev = scev.getSCEVAtScope(point->pointerOperand, loop);
                        auto baseScev = scev.getPointerBase(operandScev);
                        if (!llvm::isa<llvm::SCEVUnknown>(baseScev)) {
                            llvm::outs() << "operandScev: " << *operandScev << "\n";
                            llvm::outs() << "baseScev: " << *baseScev << "\n";
                            HANDLE_UNKOWN_VALUE(point->pointerOperand);
                        }

                        if (auto addrec = llvm::dyn_cast<llvm::SCEVAddRecExpr>(operandScev)) {
                            operandDependsOnIV += !i;
                            // figure out the trip count & evaluate the addrec at that iteration
                            auto backEdgeTakenScev = scev.getBackedgeTakenCount(loop);
                            if (!llvm::isa<llvm::SCEVCouldNotCompute>(backEdgeTakenScev))
                                backEdgeTakenScev = scev.getSCEVAtScope(backEdgeTakenScev, loop);
                            if (llvm::isa<llvm::SCEVCouldNotCompute>(backEdgeTakenScev)) {
                                cantComputeBackEdgeCount += !i;
                                // pointer depends on IV but the loop's end condition does not. 
                                // e.g., bzip2's uInt64_toAscii
                                // if we can detect the loop's first & last iteration, we could optimize this
                            } else {
                                if (hoistable) {
                                    auto exitVal = addrec->evaluateAtIteration(backEdgeTakenScev, scev);
                                    exitVal = scev.getSCEVAtScope(exitVal, loop);
                                    if (auto exitPointer = tryExpandSCEV(module, MAM, exitVal, llvm::Type::getInt8PtrTy(context, llvm::cast<llvm::PointerType>(point->pointerOperand->getType())->getAddressSpace()), preheader->getTerminator())) {
                                        exitValueComputed += !i;

                                        // insert the base
                                        auto base = llvm::cast<llvm::SCEVUnknown>(baseScev)->getValue();
                                        assert(domTree.dominates(base, preheader->getTerminator()));
                                        point->insertBefore = preheader->getTerminator();
                                        point->pointerOperand = base;
                                        ASSERT_ELSE_UNKOWN(exitPointer != base, exitPointer);

                                        // insert the log of the exit pointer
                                        // this is temporary, we can create a better packet format some day that doesn't skip over blocks
                                        assert(pointToInstructions.count(point));
                                        auto exitPoint = new InstrumentationPoint(*point);
                                        exitPoint->pointerOperand = exitPointer;
                                        pointsToInsert[exitPoint] = pointToInstructions[point];
                                        change = true;
                                    } else {
                                        unexpandableExitvalue += !i;
                                    }
                                } else {
                                    // once again, we have to find the first & last accessed memory location here,
                                    // which is way too hard if we dont know that it will be accessed on every iteration
                                }
                            }

                        } else { // while loops etc? or loads/calls
                            // this means there is no dependence on the IV, and the operand rather 
                            // depends on some loaded value or return value or something. dont know
                            // how to handle this right now.
                            // maybe also things that are phinodes? that switch targets every iteration or smt?

                            // possible constructs:
                            // index is loaded from memory, SCEV cant prove that the access pattern is linear (bsNEEDW macro in bzip)
                            // index is incremented depending on switch/condition -> SCEV cant find clear recurrence (hmmer's GCGBinaryToSequence)
                            //      -> if we recognize this, we can hoist it with range detection
                            // index is changed in weird or non-incremental ways -> SCEV cant detect recurrence (gobmk's mark_string in board.c)
                            // 
                            operandDoesNotDependOnIV += !i;
                            ivIndependentPoints.insert(point);
                        }
                    }
                }
            }

            if (!pointsToInsert.empty())
                assert(change);
            for (auto& [point, insts] : pointsToInsert)
                pointToInstructions[point].insert(insts.begin(), insts.end());
            i++;
        } while (change);

        auto oldNumInsts = instPoints.size();
        instPoints.clear();
        for (auto& [point, insts] : pointToInstructions)
            for (auto inst : insts)
                instPoints[inst].insert(point);
        
        // I think the number of described accesses should not change!
        assert(oldNumInsts == instPoints.size());
    }

#if DEBUG_IV_INDEPENDENT_LOGS
    if (!ivIndependentLogs.empty()) {
        auto smallest = *ivIndependentLogs.begin();
        for (auto log : ivIndependentLogs)
            if (log->getFunction()->size() < smallest->getFunction()->size())
                smallest = log;
        
        llvm::raw_fd_ostream currentModuleOutputfile("currentmodule.debug.ll", code);
        assert(code.value() == 0);
        module.print(currentModuleOutputfile, nullptr);
        llvm::outs() << "In function: '" << smallest->getFunction()->getName() << "'\n";
        HANDLE_UNKOWN_VALUE(smallest);
    }
#endif

    llvm::outs() << logsInLoops << " logs in loops:\n";
    llvm::outs() << "\t"<< (hoistedLogs + noMustExecuteLoopInvariant) << "/" << logsInLoops << " are loop invariant.\n";
        llvm::outs() << "\t\t" << hoistedLogs << "/" << (hoistedLogs + noMustExecuteLoopInvariant) << " hoisted to preheader.\n";
        llvm::outs() << "\t\t" << noMustExecuteLoopInvariant << "/" << (hoistedLogs + noMustExecuteLoopInvariant) << " are not guaranteed to execute.\n";
    llvm::outs() << "\t" << operandDependsOnIV << "/" << logsInLoops << " depend on the IV.\n";
        llvm::outs() << "\t\t" << cantComputeBackEdgeCount << "/" << operandDependsOnIV << " have no computable backEdgeTakenCount\n";
        llvm::outs() << "\t\t" << "We can compute " << (operandDependsOnIV - cantComputeBackEdgeCount) << "/" << operandDependsOnIV << " backEdgeTakenCounts.\n";
            llvm::outs() << "\t\t\t" << (unexpandableExitvalue + exitValueComputed) << "/" << operandDependsOnIV << " must execute once the preheader is reached.\n";
                llvm::outs() << "\t\t\t\t" << exitValueComputed << "/" << (unexpandableExitvalue + exitValueComputed) << " can be expanded & hoisted\n";

    llvm::outs() << "\t" << operandDoesNotDependOnIV << "/" << logsInLoops << " DO NOT depend on the IV.\n";
}
