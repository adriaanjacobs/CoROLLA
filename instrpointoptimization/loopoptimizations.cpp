#include <llvm-utils/instrpointoptimization/hoistloopmemaccesses.h>

#include <llvm-utils/util.h>
#include <llvm-utils/reachability/cfg_reachability.h>
#include <llvm-utils/pointerdetection/pointerdetection.h>

#include <llvm/Transforms/Utils/ScalarEvolutionExpander.h>
#include <llvm/IR/Verifier.h>


llvm::Value* tryExpandSCEV(llvm::Module& module, llvm::ModuleAnalysisManager& MAM, const llvm::SCEV* scevVal, llvm::Type* expandedTy, llvm::Instruction* insertBefore) {
    assert(!llvm::isa<llvm::SCEVCouldNotCompute>(scevVal));
    if (auto scevUnkown = llvm::dyn_cast<llvm::SCEVUnknown>(scevVal))
        return scevUnkown->getValue();
    auto& domTree = getFAM(module, MAM).getResult<llvm::DominatorTreeAnalysis>(*insertBefore->getFunction());
    auto& scev = getFAM(module, MAM).getResult<llvm::ScalarEvolutionAnalysis>(*insertBefore->getFunction());
    if (llvm::isa<llvm::SCEVAddExpr, llvm::SCEVAddRecExpr, llvm::SCEVUMinExpr, llvm::SCEVUMaxExpr>(scevVal)) {
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

    size_t pointsInLoops = 0;
    size_t hoistedPoints = 0;
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

            auto& loopInfo = FAM.getResult<llvm::LoopAnalysis>(*func);
            auto& domTree = FAM.getResult<llvm::DominatorTreeAnalysis>(*func);
            
            { // delete split-dominated points
                // we do this earlier as well, but these loop-transformations might re-introduce cases

                llvm::DenseMap<llvm::Value*, llvm::DenseSet<InstrumentationPoint*>> ptrToPoints;
                for (auto& [point, _] : pointToInstructions) 
                    ptrToPoints[pointerDetector.strip_pointer_casts(point->pointerOperand)].insert(point);
                for (auto& [_, points] : ptrToPoints) {
                    // it's possible that the summarization transformation resulted in multiple of the same points at the same location
                    // fix up places where that happened

                    llvm::DenseMap<llvm::Instruction*, llvm::DenseSet<InstrumentationPoint*>> insertBfToPoints;
                    for (auto point : points)
                        insertBfToPoints[point->insertBefore].insert(point);
                    
                    for (auto& [insertBefore, points] : insertBfToPoints) {
                        // use the first point for all relevant instructions
                        for (auto it = std::next(points.begin()); it != points.end(); ) {
                            assert(pointToInstructions.count(*it));
                            auto instsTracked = pointToInstructions[*it];
                            assert(pointToInstructions.count(*points.begin()));
                            pointToInstructions[*points.begin()].insert(instsTracked.begin(), instsTracked.end());
                            pointToInstructions.erase(*it);
                            points.erase(it++);
                            change = true;
                        }

                        assert(points.size() == 1);
                    }

                    // no location contains multiple of the same points

                    // is it possible to reach each point from the function entry without passing through any of the other points?
                    llvm::DenseSet<llvm::Instruction*> exclusionSet;
                    for (auto point : points)
                        exclusionSet.insert(point->insertBefore);
                    auto funcStart = &func->getEntryBlock().front();
                    // if any of the points is the function start, it should be the only point
                    if (exclusionSet.contains(funcStart)) {
                        assert(points.size() == 1);
                    } else {
                        for (auto point : points) {
                            bool erased = exclusionSet.erase(point->insertBefore);
                            assert(erased);
                            if (!::isPotentiallyReachable(funcStart, point->insertBefore, exclusionSet, &domTree, &loopInfo)) {
                                // point is not reachable, delete it
                                pointToInstructions.erase(point);
                                change = true;
                            }
                            exclusionSet.insert(point->insertBefore);
                        }
                    }
                }
            }

            llvm::DenseMap<llvm::Loop*, llvm::DenseSet<InstrumentationPoint*>> hoistablePoints;
            { // then, we do the split-postdom preheader check, to maximally hoist non-mustExecute points
                llvm::DenseMap<llvm::Value*, llvm::DenseSet<InstrumentationPoint*>> ptrToPoints;
                for (auto& [point, _] : pointToInstructions) 
                    ptrToPoints[pointerDetector.strip_pointer_casts(point->pointerOperand)].insert(point);
                
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
                        // are any of the function exits reachable from the preheader without going through the original point?
                        // if not -> we can safely move this point to the preheader
                        auto anyTermReachable = llvm::any_of(funcTerminators, [&] (llvm::Instruction* term) -> bool {
                            return !exclusionSet.contains(&preheader->front()) && ::isPotentiallyReachable(&preheader->front(), term, exclusionSet, &domTree, &loopInfo);
                        });
                        if (!anyTermReachable) {
                            // we can safely move this point to the preheader
                            // only insert the point once: erase all except 1 from the func points
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

            }

            auto isHoistable = [&] (InstrumentationPoint* point) -> bool {
                auto loop = loopInfo.getLoopFor(point->insertBefore->getParent());
                assert(loop);
                if (!hoistablePoints.count(loop))
                    return false;
                return hoistablePoints[loop].contains(point);
            };

            // then, we do the more classic summarization and IV-independent hoisting
            llvm::DenseMap<InstrumentationPoint*, llvm::DenseSet<llvm::Instruction*>> pointsToInsert;
            llvm::DenseSet<InstrumentationPoint*> ivIndependentPoints;
            for (auto& [point, _] : pointToInstructions) {
                if (auto loop = loopInfo.getLoopFor(point->insertBefore->getParent())) {
                    // gcc has loops which dont seem to be in this form
                    // assert(loop->isLoopSimplifyForm());
                    pointsInLoops += !i;
                    auto preheader = loop->getLoopPreheader();
                    assert(preheader);
                    assert(point->insertBefore->getParent() != preheader);
                    assert(loop->getHeader());

                    // sanity check that mustExecute points are always hoistable!!
                    const bool hoistable = isHoistable(point);
                    {
                        llvm::MustBeExecutedContextExplorer explorer = getMustBeExecutedContextExplorer(FAM, true, false);
                        bool pointMustExecute = explorer.findInContextOf(point->insertBefore, preheader->getTerminator());
                        if (pointMustExecute) {
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
                            hoistedPoints += !i;
                            change = true;
                        } else noMustExecuteLoopInvariant += !i;
                    } else {
                        auto& scev = FAM.getResult<llvm::ScalarEvolutionAnalysis>(*func);
                        auto operandScev = scev.getSCEVAtScope(point->pointerOperand, loop);
                        if (auto addrec = llvm::dyn_cast<llvm::SCEVAddRecExpr>(operandScev)) {
                            operandDependsOnIV += !i;
                            // figure out the trip count & evaluate the addrec at that iteration
                            auto backEdgeTakenScev = scev.getBackedgeTakenCount(loop);
                            if (llvm::isa<llvm::SCEVCouldNotCompute>(backEdgeTakenScev)) {
                                cantComputeBackEdgeCount += !i;
                                // pointer depends on IV but the loop's end condition does not. 
                                // e.g., bzip2's uInt64_toAscii
                                // if we can detect the loop's first & last iteration, we could optimize this
                            } else {
                                if (hoistable) {
                                    // inspired by LLVM's RuntimePointerChecking::insert()
                                    auto lowerScev = addrec->getStart();
                                    auto upperScev = addrec->evaluateAtIteration(backEdgeTakenScev, scev);

                                    // For expressions with negative step, the bounds are swapped
                                    // if the step size is constant, it's simple
                                    if (auto constStepScev = llvm::dyn_cast<llvm::SCEVConstant>(addrec->getStepRecurrence(scev))) {
                                        if (constStepScev->getValue()->isNegative())
                                            std::swap(lowerScev, upperScev);
                                    } else { // non-constant step: use umin/umax to swap them around appropriately
                                        lowerScev = scev.getUMinExpr(lowerScev, upperScev);
                                        upperScev = scev.getUMaxExpr(addrec->getStart(), upperScev);
                                    }

                                    // now, lowerScev < upperScev
                                    auto lowerVal = tryExpandSCEV(module, MAM, lowerScev, llvm::Type::getInt8PtrTy(context, llvm::cast<llvm::PointerType>(point->pointerOperand->getType())->getAddressSpace()), preheader->getTerminator());
                                    auto upperVal = tryExpandSCEV(module, MAM, upperScev, llvm::Type::getInt8PtrTy(context, llvm::cast<llvm::PointerType>(point->pointerOperand->getType())->getAddressSpace()), preheader->getTerminator());

                                    if (lowerVal && upperVal) {
                                        exitValueComputed += !i;

                                        if (lowerVal == upperVal && !backEdgeTakenScev->isZero()) {
                                            // it _can_ happen (e.g. add64 in mbedtls' MPI code) that we end up with a single-iteration loop
                                            // in that case, it's basically not a loop 
                                            // we emit the evidence twice in this case, the next iteration's split-dominance check will remove one 
                                            llvm::outs() << "operandScev: " << *addrec << "\n";
                                            llvm::outs() << "backEdgeTakenScev: " << *backEdgeTakenScev << "\n";
                                            llvm::outs() << "lowerScev: " << *lowerScev << "\n";
                                            llvm::outs() << "upperScev: " << *upperScev << "\n";
                                            llvm::outs() << "lowerVal == upperVal: " << *lowerVal << "\n";
                                            ASSERT_ELSE_UNKOWN(lowerVal != upperVal, lowerVal);
                                        }
                                        
                                        // insert the evidence for the lowerVal
                                        point->insertBefore = preheader->getTerminator();
                                        point->pointerOperand = lowerVal;

                                        // insert the evidence for the upperVal
                                        // this is temporary, we can create a better packet format some day that doesn't skip over blocks
                                        assert(pointToInstructions.count(point));
                                        auto exitPoint = new InstrumentationPoint(*point);
                                        exitPoint->pointerOperand = upperVal;
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

        // update the output parameter with the new instpoints
        instPoints.clear();
        for (auto& [point, insts] : pointToInstructions)
            for (auto inst : insts)
                instPoints[inst].insert(point);
        
        // the number of described instructions can be different here than originally,
        // because the split-dom check might remove points entirely
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

    llvm::outs() << pointsInLoops << " points in loops:\n";
    llvm::outs() << "\t"<< (hoistedPoints + noMustExecuteLoopInvariant) << "/" << pointsInLoops << " are loop invariant.\n";
        llvm::outs() << "\t\t" << hoistedPoints << "/" << (hoistedPoints + noMustExecuteLoopInvariant) << " hoisted to preheader.\n";
        llvm::outs() << "\t\t" << noMustExecuteLoopInvariant << "/" << (hoistedPoints + noMustExecuteLoopInvariant) << " are not guaranteed to execute.\n";
    llvm::outs() << "\t" << operandDependsOnIV << "/" << pointsInLoops << " depend on the IV.\n";
        llvm::outs() << "\t\t" << cantComputeBackEdgeCount << "/" << operandDependsOnIV << " have no computable backEdgeTakenCount\n";
        llvm::outs() << "\t\t" << "We can compute " << (operandDependsOnIV - cantComputeBackEdgeCount) << "/" << operandDependsOnIV << " backEdgeTakenCounts.\n";
            llvm::outs() << "\t\t\t" << (unexpandableExitvalue + exitValueComputed) << "/" << operandDependsOnIV << " must execute once the preheader is reached.\n";
                llvm::outs() << "\t\t\t\t" << exitValueComputed << "/" << (unexpandableExitvalue + exitValueComputed) << " can be expanded & hoisted\n";

    llvm::outs() << "\t" << operandDoesNotDependOnIV << "/" << pointsInLoops << " DO NOT depend on the IV.\n";
}
