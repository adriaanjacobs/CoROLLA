#include <llvm-utils/instrpointoptimization/hoistloopmemaccesses.h>

#include <llvm-utils/util.h>
#include <llvm-utils/reachability/cfg_reachability.h>
#include <llvm-utils/pointerdetection/pointerdetection.h>
#include <llvm-utils/instrpointoptimization/dominationpruning.h>

#include <llvm/Transforms/Utils/ScalarEvolutionExpander.h>
#include <llvm/IR/Verifier.h>

LoopHoister<llvm::Function>::LoopHoister(llvm::Function& F, llvm::FunctionAnalysisManager& FAM, const PointerDetector* pointerDetector) : 
    function{F}, FAM{FAM}, 
    SCEV{FAM.getResult<llvm::ScalarEvolutionAnalysis>(F)}, 
    SCEVExpander{SCEV, F.getParent()->getDataLayout(), "expanded"},
    pointerDetector{pointerDetector}
{}

llvm::Value* LoopHoister<llvm::Function>::tryExpandSCEV(const llvm::SCEV* scevVal, llvm::Type* expandedTy, llvm::Instruction* insertBefore) {
    assert(!llvm::isa<llvm::SCEVCouldNotCompute>(scevVal));
    if (auto scevUnkown = llvm::dyn_cast<llvm::SCEVUnknown>(scevVal))
        return scevUnkown->getValue();
    auto& domTree = FAM.getResult<llvm::DominatorTreeAnalysis>(*insertBefore->getFunction());
    auto& SCEV = FAM.getResult<llvm::ScalarEvolutionAnalysis>(*insertBefore->getFunction());
    if (llvm::isa<llvm::SCEVAddExpr, llvm::SCEVAddRecExpr, llvm::SCEVUMinExpr, llvm::SCEVUMaxExpr>(scevVal)) {
        // that's okay
        auto value = SCEVExpander.expandCodeFor(scevVal, expandedTy, insertBefore);

        auto isns = SCEVExpander.getAllInsertedInstructions();
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
            SCEVExpander.clear();
            return nullptr;
        } else return value;
    } else HANDLE_UNKOWN_SCEV(scevVal);
}

// we use this to determine a suitable useToReplace for range checks
//  this function therefore heavily assumes that the pointerOperand is an addrec for loop
llvm::Use* LoopHoister<llvm::Function>::findLoopInvariantPointerBaseUse(llvm::Loop* loop, llvm::Value* pointerOperand) {
    auto isInLoop = [&] (llvm::Value* val) -> bool {
        auto inst = llvm::dyn_cast<llvm::Instruction>(val);
        return inst && loop->contains(inst);
    };

    // find the use that feeds this pointerBase into the loop recurrence
    auto current = llvm::cast<llvm::Instruction>(pointerOperand);
    while (true) {
        // go through operations until we find a loop-bound instruction that introduces this pointerBase
        ASSERT_ELSE_UNKOWN(loop->contains(current), current);
        if (auto gep = llvm::dyn_cast<llvm::GetElementPtrInst>(current)) {
            if (!isInLoop(gep->getPointerOperand()))
                return &gep->getOperandUse(gep->getPointerOperandIndex());
            current = llvm::cast<llvm::Instruction>(gep->getPointerOperand());
        } else if (auto phi = llvm::dyn_cast<llvm::PHINode>(current)) {
            llvm::DenseSet<llvm::Use*> uses;
            for (auto& incomingUse : phi->incoming_values())
                if (!isInLoop(incomingUse.get()))
                    uses.insert(&incomingUse);
            // if >1: is the loop canonical? i expect only a single incoming edge from outside
            // if 0: how could it be an addrec if the pointer is dependent on multiple phis?
            ASSERT_ELSE_UNKOWN(uses.size() == 1, phi);
            return *uses.begin();
        } else if (auto bitcast = llvm::dyn_cast<llvm::BitCastInst>(current)) {
            current = llvm::cast<llvm::Instruction>(bitcast->getOperand(0));
        } else HANDLE_UNKOWN_VALUE(current);
    }
}

llvm::Value* LoopHoister<llvm::Function>::computeICMP(llvm::ICmpInst::Predicate pred, llvm::Value* lhs, llvm::Value* rhs, llvm::Instruction* insertBefore) {
    auto int8PtrTy = llvm::Type::getInt8PtrTy(insertBefore->getContext());
    lhs = createBitOrPointerCastIfNecessary(lhs, int8PtrTy, "", insertBefore);
    rhs = createBitOrPointerCastIfNecessary(rhs, int8PtrTy, "", insertBefore);
    auto cmp = new llvm::ICmpInst(insertBefore, pred, lhs, rhs);
    auto select = llvm::SelectInst::Create(cmp, lhs, rhs, "", insertBefore);
    return select;
}

LoopHoister<llvm::Function>::Stats LoopHoister<llvm::Function>::hoistLoopBoundMemAccesses(llvm::DenseMap<llvm::Use*, InstrumentationPoint*>& useToPoint, bool permitNonMustExecute) {
    auto& context = function.getContext();

    Stats stats{};

    auto stripPointerCasts = [&] (llvm::Value* ptr) -> llvm::Value* {
        if (pointerDetector)
            return pointerDetector->strip_pointer_casts(ptr);
        auto retval = ptr->stripPointerCastsForAliasAnalysis();
        assert(retval);
        return retval;
    };

    // which instrumentation point descibes which use
    llvm::DenseMap<InstrumentationPoint*, llvm::DenseSet<llvm::Use*>> pointToUses;
    for (auto& [use, point] : useToPoint) {
        pointToUses[point].insert(use);
    }

    bool change = false;
    int i = 0;

    llvm::DenseSet<llvm::Instruction*> funcTerminators;
    for (auto& bb : function) 
        if (llvm::isa<llvm::UnreachableInst, llvm::ReturnInst>(bb.getTerminator()))
            funcTerminators.insert(bb.getTerminator());

    llvm::DenseMap<llvm::Use*, InstrumentationPoint*> surrogateUseToPoint;

    do {
        change = false;

        auto& loopInfo = FAM.getResult<llvm::LoopAnalysis>(function);
        auto& domTree = FAM.getResult<llvm::DominatorTreeAnalysis>(function);

        { // sanity check the input here: all points should always dominate their uses
            auto insertBfDominates = [&] (InstrumentationPoint* point, llvm::Use* use) -> bool {
                return point->insertBefore == use->getUser() || domTree.dominates(point->insertBefore, *use);
            };
            for (auto& [point, uses] : pointToUses) 
                for (auto& use : uses) 
                    assert(insertBfDominates(point, use));
        }
        
        { // delete split-dominated points
            // we do this earlier as well, but these loop-transformations might re-introduce cases
            if (pruneDominatedChecks(pointToUses, stripPointerCasts, domTree, loopInfo))
                change = true;
        }

        llvm::DenseMap<llvm::Loop* /* loop containing these */, llvm::DenseSet<InstrumentationPoint*>> hoistablePoints;
        { // then, we do the split-postdom preheader check, to maximally hoist non-mustExecute points
            // the basic idea is that the same check might be performed on every possible path through the function
            //  in that case, we can still hoist the loop-bound ones into the preheader of their loop: they would execute anyway
            //  (even though they may not postdominate the loop preheader themselves)
            //  very useful for code like:
            //
            //  while (...) 
            //      if (...)
            //          check();
            //      else
            //          check();
            //
            //  neither of the checks postdominate the preheader invididually, but both together totally do. 
            //  they might _still_ not be hoistable though, e.g., if the check happens on a loop-variant pointer. 

            llvm::DenseMap<llvm::Value*, llvm::DenseSet<InstrumentationPoint*>> ptrToPoints;
            for (auto& [point, _] : pointToUses) 
                ptrToPoints[stripPointerCasts(point->pointerOperand)].insert(point);
            
            for (auto& [_, samePtrPoints] : ptrToPoints) {
                llvm::DenseSet<llvm::Instruction*> exclusionSet;
                for (auto point : samePtrPoints)
                    exclusionSet.insert(point->insertBefore);

                llvm::DenseMap<llvm::Loop*, llvm::DenseSet<InstrumentationPoint*>> loopBoundPoints;
                for (auto point : samePtrPoints)
                    if (auto loop = loopInfo.getLoopFor(point->insertBefore->getParent()))
                        loopBoundPoints[loop].insert(point);
                
                for (auto& [loop, loopPoints] : loopBoundPoints) {
                    // all of these loopPoints have the same ptrOperand and occur in the same loop.
                    assert(!loopPoints.empty());
                    auto preheader = loop->getLoopPreheader();
                    assert(preheader);
                    assert(!funcTerminators.empty());
                    // are any of the function exits reachable from the preheader without going through the original point?
                    // if not -> we might be able to move this point to the preheader
                    auto anyTermReachable = llvm::any_of(funcTerminators, [&] (llvm::Instruction* term) -> bool {
                        return !exclusionSet.contains(&preheader->front()) && ::isPotentiallyReachable(&preheader->front(), term, exclusionSet, &domTree, &loopInfo);
                    });
                    if (!anyTermReachable) {
                        // we might be able to move this point to the preheader
                        //  !! only if the ptrOperand itself can be constructed outside the loop
                        // we mark these as hoistable and let the later instrumentation figure out 
                        //  whether it's actually true.
                        // this will result in multiple copies of the same check in the preheader,
                        //  but the next iteration should filter that out
                        assert(!loopPoints.empty());
                        for (auto loopPoint : loopPoints) {
                            // range checks can be used as part of the split-postdom front, but
                            //  they cannot comprehensively cancel each other out
                            //  we leave the overlap analysis that would more comprehensively do this
                            //  for a later day
                            // however, this doesn't mean that we cant hoist range checks. 
                            //  if the range check is alone here, it is not a split-postdom, 
                            //  and it should be hoistable!
                            if (!loopPoint->isRangeCheck() || loopPoints.size() == 1)
                                hoistablePoints[loop].insert(loopPoint);
                        }
                    }
                }
            }
        }

        auto isHoistable = [&] (InstrumentationPoint* point) -> bool {
            auto loop = loopInfo.getLoopFor(point->insertBefore->getParent());
            assert(loop);
            if (!hoistablePoints.count(loop))
                return false;
            return hoistablePoints.find(loop)->getSecond().contains(point);
        };

        // then, we do the more classic summarization and IV-independent hoisting
        llvm::DenseSet<InstrumentationPoint*> ivIndependentPoints;
        llvm::DenseSet<InstrumentationPoint*> toErase;
        for (auto& [point, pointUses] : pointToUses) {
            // both pointer operands would need to satisfy the conditions for hoisting
            //  that's currently not implemented, so we skip the rangechecks here
            if (point->isRangeCheck()) 
                continue;

            if (auto loop = loopInfo.getLoopFor(point->insertBefore->getParent())) {
                // gcc has loops which dont seem to be in this form
                // assert(loop->isLoopSimplifyForm());
                stats[pointsInLoops] += !i;
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

                assert(!point->isRangeCheck()); // should not get here
                if (loop->isLoopInvariant(point->pointerOperand)) {
                    if (permitNonMustExecute || hoistable) {
                        assert(domTree.dominates(point->pointerOperand, preheader->getTerminator()));
                        point->insertBefore = preheader->getTerminator();
                        // record any "forced" hoisting in case the instrumentation wants to treat it differently 
                        if (!point->unsoundlyHoisted) 
                            point->unsoundlyHoisted = !hoistable;
                        stats[hoistedLIPoints] += !i;
                        stats[unsoundlyHoistedPoints] += !i && !hoistable;
                        change = true;
                    } else stats[noMustExecuteLoopInvariant] += !i;
                } else {
                    auto operandScev = SCEV.getSCEVAtScope(point->pointerOperand, loop);
                    if (auto addrec = llvm::dyn_cast<llvm::SCEVAddRecExpr>(operandScev)) {
                        stats[operandDependsOnIV] += !i;
                        // figure out the trip count & evaluate the addrec at that iteration
                        auto backEdgeTakenScev = SCEV.getBackedgeTakenCount(loop);
                        if (llvm::isa<llvm::SCEVCouldNotCompute>(backEdgeTakenScev)) {
                            stats[cantComputeBackEdgeCount] += !i;
                            // pointer depends on IV but the loop's end condition does not. 
                            // e.g., bzip2's uInt64_toAscii
                            // if we can detect the loop's first & last iteration, we could optimize this
                        } else {
                            if (hoistable) {
                                // inspired by LLVM's RuntimePointerChecking::insert()
                                auto lowerScev = addrec->getStart();
                                auto upperScev = addrec->evaluateAtIteration(backEdgeTakenScev, SCEV);

                                // For expressions with negative step, the bounds are swapped
                                // if the step size is constant, it's simple
                                if (auto constStepScev = llvm::dyn_cast<llvm::SCEVConstant>(addrec->getStepRecurrence(SCEV))) {
                                    if (constStepScev->getValue()->isNegative())
                                        std::swap(lowerScev, upperScev);
                                } else { // non-constant step: use umin/umax to swap them around appropriately
                                    lowerScev = SCEV.getUMinExpr(lowerScev, upperScev);
                                    upperScev = SCEV.getUMaxExpr(addrec->getStart(), upperScev);
                                }

                                // now, lowerScev < upperScev
                                auto pointerType = llvm::Type::getInt8PtrTy(context, llvm::cast<llvm::PointerType>(point->pointerOperand->getType())->getAddressSpace());
                                auto lowerVal = tryExpandSCEV(lowerScev, pointerType, preheader->getTerminator());
                                auto upperVal = tryExpandSCEV(upperScev, pointerType, preheader->getTerminator());

                                if (lowerVal && upperVal) {
                                    stats[exitValueComputed] += !i;

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

                                    // find the new useToReplace
                                    auto surrogateUse = findLoopInvariantPointerBaseUse(loop, point->pointerOperand);
                                    assert(!pointUses.contains(surrogateUse));

                                    if (auto surrogatePointIt = surrogateUseToPoint.find(surrogateUse); surrogatePointIt != surrogateUseToPoint.end()) {
                                        auto surrogatePoint = surrogatePointIt->getSecond();
                                        // this surrogateUse is already described by a previous point. 
                                        //  Naturally, this previous point describes the same memory accesses as this one
                                        //  find out the min,max bounds of both of them and update this point to range-check both of them at once
                                        auto combinedLower = computeICMP(llvm::ICmpInst::ICMP_ULT, surrogatePoint->pointerOperand, lowerVal, preheader->getTerminator());
                                        auto combinedUpper = computeICMP(llvm::ICmpInst::ICMP_UGT, surrogatePoint->endOfAddressRange, upperVal, preheader->getTerminator());
                                        surrogatePoint->pointerOperand = combinedLower;
                                        surrogatePoint->endOfAddressRange = combinedUpper;
                                        // delete the point we just replaced
                                        toErase.insert(point);
                                    } else {
                                        // this is the first point for this surrogateuse
                                        // replace all loop uses for this point with the surrogateuse
                                        llvm::DenseSet<llvm::Use*> toErase;
                                        for (auto& use : pointUses)
                                            if (auto inst = llvm::dyn_cast<llvm::Instruction>(use->getUser()); inst && loop->contains(inst))
                                                toErase.insert(use);
                                        for (auto use : toErase)
                                            pointUses.erase(use);
                                        assert(pointUses.empty()); // i can't imagine there are non-loop-bound uses for this pointerOperand??
                                        pointUses.insert(surrogateUse);

                                        auto dbg = surrogateUseToPoint.try_emplace(surrogateUse, point).second;
                                        assert(dbg);
                                        // update the point with the lower & higher range bounds
                                        assert(!point->isRangeCheck());
                                        point->insertBefore = preheader->getTerminator();
                                        point->pointerOperand = lowerVal;
                                        point->endOfAddressRange = upperVal;
                                    }

                                    change = true;
                                } else {
                                    stats[unexpandableExitvalue] += !i;
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
                        stats[operandDoesNotDependOnIV] += !i;
                        ivIndependentPoints.insert(point);
                    }
                }
            }
        }

        for (auto point : toErase)
            pointToUses.erase(point);

        i++;
    } while (change);

    // update the output parameter with the new instpoints
    useToPoint.clear();
    for (auto& [point, uses] : pointToUses)
        for (auto use : uses) {
            if (useToPoint.count(use)) {
                llvm::errs() << "use already described by another point!\n";
                llvm::errs() << "use: operand " << use->getOperandNo() << " of " << *use->getUser() << "\n";
                llvm::errs() << "existing point:\n";
                useToPoint.find(use)->getSecond()->print();
                llvm::errs() << "new point:\n";
                point->print();
                HANDLE_UNKOWN_VALUE(use->getUser());
            }
            ASSERT_ELSE_UNKOWN(!useToPoint.count(use), use->getUser());
            useToPoint[use] = point;
        }
    
    // the number of described instructions can be different here than originally,
    // because the split-dom check might remove points entirely

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

    return stats;
}


LoopHoister<llvm::Module>::LoopHoister(llvm::Module& M, llvm::ModuleAnalysisManager& MAM) : 
    module{M}, MAM{MAM}
{}

void LoopHoister<llvm::Module>::hoistLoopBoundMemAccesses(llvm::DenseMap<llvm::Function*, llvm::DenseMap<llvm::Use*, InstrumentationPoint*>>& funcToInstPoints, bool permitNonMustExecute, const PointerDetector* pointerDetector) {
    LoopHoister<llvm::Function>::Stats stats{};
    for (auto& [func, useToPoint] : funcToInstPoints) {
        auto [it, inserted] = funcHoisters.try_emplace(func, *func, getFAM(module, MAM), pointerDetector);
        auto funcStats = it->second.hoistLoopBoundMemAccesses(useToPoint, permitNonMustExecute);
        stats += funcStats;
    }

    using enum LoopHoister<llvm::Function>::StatCounter;

    llvm::outs() << stats[pointsInLoops] << " points in loops:\n";
    llvm::outs() << "\t"<< (stats[hoistedLIPoints] + stats[noMustExecuteLoopInvariant]) << "/" << stats[pointsInLoops] << " are loop invariant.\n";
        llvm::outs() << "\t\t" << stats[hoistedLIPoints] << "/" << (stats[hoistedLIPoints] + stats[noMustExecuteLoopInvariant]) << " hoisted to preheader "
                    << "(" << stats[unsoundlyHoistedPoints] << " unsoundly).\n";
        llvm::outs() << "\t\t" << stats[noMustExecuteLoopInvariant] << "/" << (stats[hoistedLIPoints] + stats[noMustExecuteLoopInvariant]) << " are not guaranteed to execute.\n";
    llvm::outs() << "\t" << stats[operandDependsOnIV] << "/" << stats[pointsInLoops] << " depend on the IV.\n";
        llvm::outs() << "\t\t" << stats[cantComputeBackEdgeCount] << "/" << stats[operandDependsOnIV] << " have no computable backEdgeTakenCount\n";
        llvm::outs() << "\t\t" << "We can compute " << (stats[operandDependsOnIV] - stats[cantComputeBackEdgeCount]) << "/" << stats[operandDependsOnIV] << " backEdgeTakenCounts.\n";
            llvm::outs() << "\t\t\t" << (stats[unexpandableExitvalue] + stats[exitValueComputed]) << "/" << stats[operandDependsOnIV] << " must execute once the preheader is reached.\n";
                llvm::outs() << "\t\t\t\t" << stats[exitValueComputed] << "/" << (stats[unexpandableExitvalue] + stats[exitValueComputed]) << " can be expanded & hoisted\n";

    llvm::outs() << "\t" << stats[operandDoesNotDependOnIV] << "/" << stats[pointsInLoops] << " DO NOT depend on the IV.\n";
}
