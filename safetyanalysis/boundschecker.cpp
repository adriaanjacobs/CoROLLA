#include <llvm-utils/safetyanalysis/safetyanalysis.h>

#include <llvm-utils/safetyanalysis/allocationbounds.h>
#include <llvm-utils/util.h>
#include <llvm-utils/pointerdetection/pointerdetection.h>
#include <llvm-utils/reachability/reachingdefinitions.h>
#include <llvm-utils/callsiteanalysis/callsiteanalysis.h>

#include <llvm/IR/Instructions.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/Analysis/StackSafetyAnalysis.h>
#include <llvm/Analysis/ScalarEvolutionExpressions.h>
#include <llvm/Analysis/MemoryDependenceAnalysis.h>
#include <llvm/Analysis/Delinearization.h>
#include <llvm/IR/Constants.h>

#include <cstdint>

llvm::AnalysisKey IsInBoundsAnalysis::Key;

void BoundsChecker::printBailStats() {
    auto statsCpy = bailStats;
    llvm::outs() << "Bail stats for isInBoundsAnalysis: \n";
    uint rank = 1;
    while (!bailStats.empty()) {
        auto maxIt = [&] {
            auto max = bailStats.begin();
            for (auto it = bailStats.begin(); it != bailStats.end(); it++)
                if (it->getSecond() > max->getSecond())
                    max = it;
            return max;
        } ();
        assert(maxIt->getFirst() != "");
        llvm::outs() << "\t#" << rank << ": " << maxIt->getFirst() << ". " << maxIt->getSecond() << " occurrences.\n";
        rank++;
        bailStats.erase(maxIt);
    }
    bailStats = statsCpy;
}

bool BoundsChecker::isInBounds(llvm::Value* offsetPtr, llvm::APInt storeSize) {
    assert(callStack.empty()); // otherwise we didnt clear something in time
    auto [ptrIt, ptrInserted] = boundsCache.try_emplace(offsetPtr);
    assert(ptrIt != boundsCache.end());
    auto [offsetIt, offsetInserted] = ptrIt->getSecond().try_emplace(storeSize, std::nullopt);
    assert(offsetIt != ptrIt->getSecond().end());

    auto isInRange = [&] (llvm::Value* current, llvm::APInt offset, DIRECTION) -> std::optional<bool> {
        if (isNonWrapperAllocSite(current)) {
            // these are other allocations, likely also in the points-to set of this pointer operand. 
            auto allocBounds = findMinimumAllocBounds(current, module, MAM);

            if (!allocBounds.has_value()) 
                return { false };
            
            bool ret = offset.sge(allocBounds.value().first) && offset.sle(allocBounds.value().second);
            if (auto alloca = llvm::dyn_cast<llvm::AllocaInst>(current)) {
                auto& stackSafety = MAM.getResult<llvm::StackSafetyGlobalAnalysis>(module);
                if(stackSafety.isSafe(*alloca))
                    assert(ret);
            }
            return {ret};
        } else return std::nullopt;
    };

    // when calling isInBounds, add the loadstoreSize to the offset for maximal.
    // don't add for minimal
    if (ptrInserted || offsetInserted) {
        assert(offsetIt->getSecond() == std::nullopt);
        // compute upper & lower inbounds. fail early
        IsInBoundsResult result;
        result = isInBounds_internal<UPPER>(offsetPtr, storeSize, isInRange);
        if (!result.inBounds)
            goto fail;
        result = isInBounds_internal<LOWER>(offsetPtr, llvm::APInt{64,0}, isInRange);
        if (!result.inBounds)
            goto fail;
        
        // both in bounds!
        offsetIt->getSecond() = IsInBoundsResult::True();
        goto past_fail;
fail:
        // update bailstats
        assert(!result.inBounds);
        offsetIt->getSecond() = result;
        assert(result.explanation != "");
        bailStats[result.explanation]++;
    }
past_fail:
    assert(offsetIt->getSecond().has_value());
    return offsetIt->getSecond().value().inBounds;
}

std::optional<BoundsChecker::IsInBoundsResult> BoundsChecker::isInCache(llvm::Value* offsetPtr, llvm::APInt offset) const {
    // don't check the cache if we're going to use calling context information
    if (llvm::isa<llvm::Argument>(offsetPtr) && !callStack.empty())
        return std::nullopt;
    
    auto ptrIt = boundsCache.find(offsetPtr);
    if (ptrIt != boundsCache.end()) {
        auto offsetIt = ptrIt->getSecond().find(offset);
        if (offsetIt != ptrIt->getSecond().end())
            return offsetIt->getSecond();
    }
    return std::nullopt;
}

llvm::StringRef getFuncName(llvm::Value* val) {
    auto func = functionOf(val);
    if (func)
        return func->getName();
    else return "Unkown";
}

bool BoundsChecker::isInRange_nonCached(llvm::Value* offsetPtr, llvm::APInt offset, const std::function<std::optional<bool>(llvm::Value*, llvm::APInt, DIRECTION)>& isInRange) {
    return isInBounds_internal<UPPER>(offsetPtr, offset, isInRange, false).inBounds && isInBounds_internal<LOWER>(offsetPtr, offset, isInRange, false).inBounds;
}

template<DIRECTION DIR>
BoundsChecker::IsInBoundsResult BoundsChecker::isInBounds_internal(llvm::Value* offsetPtr, llvm::APInt offset, const std::function<std::optional<bool>(llvm::Value*, llvm::APInt, DIRECTION)>& isInRange, bool checkTheCache) {
    struct PassedValue {
        llvm::Value* val;
        llvm::APInt offset;
    };
    static thread_local std::vector<PassedValue> passedInstrs;
    const auto numPassedValues = passedInstrs.size();
    run_on_destruct resetPassedInstrs([&](){
        assert(passedInstrs.size() >= 1);
        assert(numPassedValues <= passedInstrs.size());
        passedInstrs.erase(passedInstrs.begin() + numPassedValues, passedInstrs.end());
        assert(passedInstrs.size() == numPassedValues);
    });

    auto& dataLayout = module.getDataLayout();
    auto& context = module.getContext();
    auto& FAM = getFAM(module, MAM);

    llvm::Value* current = offsetPtr;

    while (true) {
        // check if we've seen this one before
        auto passedValIt = llvm::find_if(passedInstrs, [&] (const PassedValue& passedVal) -> bool {
            return passedVal.val == current;
        });
        if (passedValIt != passedInstrs.end()) {
            if (passedValIt->offset == offset)
                return IsInBoundsResult::True(); // dataflow back to myself with no offset difference? safe
            else 
                return IsInBoundsResult::False("recursive self-dependence with non-zero offset"); // may change offset indefinitely
        }

        auto oldCurrent = current;
        passedInstrs.push_back({current, offset});

        if (checkTheCache)
            if (auto val = isInCache(current, offset))
                return val.value();

        if (auto retVal = isInRange(current, offset, DIR)) {
            assert(retVal.has_value());
            if (retVal.value() == false)
                return IsInBoundsResult::False("alloc: not in bounds of allocsite");
            return IsInBoundsResult::True();
        } else if (llvm::isa<llvm::ConstantPointerNull, llvm::ConstantInt>(current)) {
            if (auto constInt = llvm::dyn_cast<llvm::ConstantInt>(current))
                offset += constInt->getValue();
            llvm::ConstantRange userspace({64, 8'388'608U}, {64, UINT64_MAX >> 17});
            if (userspace.contains(offset)) {
                // llvm::outs() << "Offset to NULL: " << offset << "\n";
                return IsInBoundsResult::False("constant: large fixed userpace address");
            }
            return IsInBoundsResult::True(); // the program will crash when dereferencing these anyway
        } else if (auto argument = llvm::dyn_cast<llvm::Argument>(current)) {
            ASSERT_ELSE_UNKOWN(!argument->hasByValAttr(), argument); // should have been caught by isAllocationSite already

            // check whether we can context-sensitively analyze this call
            if (!callStack.empty()) {
                auto caller = callStack.pop_back_val();
                defer (callStack.push_back(caller));
                // sanity check that we were really called from the latest callsite in the call stack
                if (auto calledFunc = caller->getCalledFunction()) // maybe we can look through some indirect calls in the future, too
                    ASSERT_ELSE_UNKOWN(calledFunc == argument->getParent(), argument);
                auto argOperand = caller->getArgOperand(argument->getArgNo());
                return isInBounds_internal<DIR>(argOperand, offset, isInRange);
            }
            
            auto& callSiteAnalysis = MAM.getResult<CallSiteAnalysis>(module); 
            llvm::DenseSet<llvm::Value*> incomingVals;
            bool isComplete = callSiteAnalysis.getIncomingValuesForArgument(argument, incomingVals);
            if (!isComplete)
                return IsInBoundsResult::False("arg: no complete callsite info");
            for (auto argOperand : incomingVals) {
                assert(argOperand->getType() == argument->getType());
                auto result = isInBounds_internal<DIR>(argOperand, offset, isInRange);
                if (!result.inBounds) 
                    return result;
            }
            return IsInBoundsResult::True();
        } else if (auto call = llvm::dyn_cast<llvm::CallBase>(current)) {
            auto knownCallees = ::getKnownCallees(call);
            if (knownCallees.empty())
                return IsInBoundsResult::False("call: unanalyzable indirect");

            for (auto calledFunc : knownCallees) {
                if (calledFunc->isDeclaration()) {
                    // if it was an allocation function, we would've found it by now
                    // maybe i can still model some common ones here?
                    if (calledFunc->getIntrinsicID() == llvm::Intrinsic::load_relative) {
                        // common case according to docs. E.g. h264ref 
                        // let's not solve this until we find a benchmark where we need to
                        if (!llvm::isa<llvm::Constant>(call->getArgOperand(1)))
                            return IsInBoundsResult::False("call: non-constant load.relative");
                    }

                    ASSERT_ELSE_UNKOWN(!calledFunc->isIntrinsic(), calledFunc);
                    ASSERT_ELSE_UNKOWN(!calledFunc->returnDoesNotAlias(), calledFunc);
                    return IsInBoundsResult::False("call: unknown external func");
                }

                // push this callsite to the callstack to inform later analysis on Arguments that they can 
                //  simply return back to this callsite
                callStack.push_back(call);
                auto size = callStack.size();
                defer (
                    // clear everything in the callstack after (and including) this frame
                    ASSERT_ELSE_UNKOWN(callStack.size() == size, call);
                    ASSERT_ELSE_UNKOWN(callStack.back() == call, call);
                    callStack.pop_back();
                );

                // check if all return values happen to be in bounds, if so we gucci
                for (auto& bb : *calledFunc) {
                    if (auto retInst = llvm::dyn_cast<llvm::ReturnInst>(bb.getTerminator())) {
                        auto retVal = retInst->getReturnValue();
                        auto retInBounds = isInBounds_internal<DIR>(retVal, offset, isInRange);
                        if (!retInBounds.inBounds)
                            return retInBounds;
                    }
                }
            }

            return IsInBoundsResult::True();
        } else if (auto gepInstr = llvm::dyn_cast<llvm::GetElementPtrInst>(current)) {
            if (gepInstr->hasAllConstantIndices()) {
                for (auto& idxuse : gepInstr->indices())
                    assert(llvm::isa<llvm::ConstantInt>(idxuse.get()));
                bool val = gepInstr->accumulateConstantOffset(dataLayout, offset);
                assert(val);
                current = gepInstr->getPointerOperand();
                continue;
            } else {
                auto& funcScev = FAM.getResult<llvm::ScalarEvolutionAnalysis>(*gepInstr->getFunction());
                llvm::SmallVector<const llvm::SCEV*> subscripts;
                llvm::SmallVector<int> sizes;
                // alternative API: scev.getGEPExpr (probably less freaky)
                bool success = llvm::getIndexExpressionsFromGEP(funcScev, gepInstr, subscripts, sizes);
                if (!success)
                    return IsInBoundsResult::False("GEP: non-constant idx expressions");
                assert(success);

                ASSERT_ELSE_UNKOWN(subscripts.size() == sizes.size() || subscripts.size() == sizes.size() + 1, gepInstr);
                ASSERT_ELSE_UNKOWN(subscripts.size() == gepInstr->getNumIndices() || subscripts.size() == gepInstr->getNumIndices() - 1, gepInstr);

                if (subscripts.size() == gepInstr->getNumIndices() - 1) {
                    auto scev = funcScev.getSCEV(gepInstr->getOperand(1));
                    assert(llvm::isa<llvm::SCEVConstant>(scev) && llvm::cast<llvm::SCEVConstant>(scev)->getValue()->isZero());
                    subscripts.insert(subscripts.begin(), scev);
                    assert(subscripts.size() >= 2);
                    assert(*subscripts.begin() == scev);
                }

                llvm::SmallVector<llvm::Value*> constantIndices;
                for (auto scev : subscripts) {
                    // TODO: fix this, not entirely accurate (lower/negative bound might be more dangerous than upper bound)
                    // BUG: This is wrong! we ignore super high values (UINT64_MAX), they just wrap on the addition later
                    //  we should detect them and bail out here (or inside getSignedSCEVLimit)
                    auto limit = getSignedSCEVLimit<DIR>(scev, funcScev);
                    if (!limit.has_value())
                        break;

                    constantIndices.push_back(llvm::ConstantInt::get(context, limit.value()));
                    assert(constantIndices.size() <= subscripts.size());
                }

                if (constantIndices.size() == subscripts.size()) {
                    auto dummyGep = llvm::GetElementPtrInst::Create(gepInstr->getSourceElementType(), gepInstr->getPointerOperand(), constantIndices);
                    assert(dummyGep->hasAllConstantIndices());
                    llvm::APInt offsetBefore = offset;
                    bool val = dummyGep->accumulateConstantOffset(dataLayout, offset);
                    assert(val);
                    current = dummyGep->getPointerOperand();
                    dummyGep->deleteValue();
                    continue;
                } else {
                    assert(constantIndices.size() < subscripts.size());
                    return IsInBoundsResult::False("GEP: unanalyzable idx expressions");
                }
                assert(false);
            }
            assert(false);
        } else if (auto loadInst = llvm::dyn_cast<llvm::LoadInst>(current)) {
            ASSERT_ELSE_UNKOWN(dataLayout.getTypeSizeInBits(loadInst->getType()) == 64, loadInst);
            /* memorySSA crashes on nginx' "ngx_master_process_cycle" function for some reason
                I cannot reproduce it with opt, but however i try to get a memorySSA for that function here, I fail
                So I am not going to give a shit and use the legacy analysis here
            */
            auto& rds = MAM.getResult<ReachingDefinitionsAnalysis>(module);
            if (auto definingPtr = rds.findDefForLoad(loadInst)) 
                return isInBounds_internal<DIR>(definingPtr, offset, isInRange);

            return IsInBoundsResult::False("load: no definer found");
        } else if (auto extractValue = llvm::dyn_cast<llvm::ExtractValueInst>(current)) {
            auto& rds = MAM.getResult<ReachingDefinitionsAnalysis>(module);
            auto defs = rds.findDefsForExtractValue(extractValue);
            if (defs.empty())
                return IsInBoundsResult::False("extractval: no definers found");

            for (auto def : defs) {
                auto defInBounds = isInBounds_internal<DIR>(def, offset, isInRange);
                if (!defInBounds.inBounds)
                    return defInBounds;
            }

            return IsInBoundsResult::True();
        } else if (llvm::isa<llvm::UndefValue>(current)) {
            return IsInBoundsResult::False("undef");
        } else if (llvm::isa<llvm::ExtractElementInst>(current)) {
            return IsInBoundsResult::False("extractel: unimplemented");
        } else if (llvm::isa<llvm::BitCastInst>(current)) {
            auto castInst = llvm::cast<llvm::CastInst>(current);
            assert(castInst->getNumOperands() == 1);
            current = castInst->getOperand(0);
            continue;
            assert(false);
        } else if (auto trunc = llvm::dyn_cast<llvm::TruncInst>(current)) {
            // benchmark.ll has the specific case where the result of int_div_int is stored as a "potential clobber"
            ASSERT_ELSE_UNKOWN(dataLayout.getTypeSizeInBits(trunc->getType()) == 64, trunc);
            ASSERT_ELSE_UNKOWN(dataLayout.getTypeSizeInBits(trunc->getOperand(0)->getType()) == 128, trunc);
            return IsInBoundsResult::False("trunc: weird trunc i128");
        } else if (auto phiNode = llvm::dyn_cast<llvm::PHINode>(current)) {
            if (auto constVal = phiNode->hasConstantValue()) {
                current = constVal;
                continue;
            } else {
                auto& loopInfo = FAM.getResult<llvm::LoopAnalysis>(*phiNode->getFunction());
                auto& SCEV = FAM.getResult<llvm::ScalarEvolutionAnalysis>(*phiNode->getFunction());
                auto phiScev = SCEV.getSCEV(phiNode);
                assert(phiScev);
                if (auto loop = loopInfo.getLoopFor(phiNode->getParent())) {
                    if (SCEV.hasComputableLoopEvolution(phiScev, loop)) {
                        assert(phiScev->getSCEVType() != llvm::scCouldNotCompute);
                        auto baseScev = SCEV.getPointerBase(phiScev);
                        assert(baseScev);
                        assert(baseScev->getSCEVType() != llvm::scCouldNotCompute);
                        if (baseScev->getSCEVType() != llvm::scUnknown) {
                            // some iterations (e.g., std::find with reverse iterator on std::vector) use an i64 instead of ptr
                            // to iterate over the array. `getPointerBase` cannot deal with that, LLVM devs don't know how to solve it
                            // https://github.com/llvm/llvm-project/issues/65743
                            // we just bail out, I guess. I think leela_s or imagick_s triggered this
                            // perlbench also had a SCEVUminExpr here. We could continue analyzing some of these, but I doubt it's worth it
                        } else {
                            assert(baseScev->getSCEVType() == llvm::scUnknown);
                            auto offsetScev = SCEV.getMinusSCEV(phiScev, baseScev);
                            assert(offsetScev && offsetScev->getSCEVType() != llvm::scCouldNotCompute);
                            auto offsetVal = getSignedSCEVLimit<DIR>(offsetScev, SCEV);
                            // there's an implicit assumption here that the pointer evolves via add's through the loop
                            // maybe we can validate this somehow by checking the scevtype of "phiScev"
                            // but I think this is guaranteed by the loopevolution definition
                            if (offsetVal.has_value()) {
                                offset += offsetVal.value();
                                if (!llvm::isa<llvm::SCEVUnknown>(baseScev)) {
                                    llvm::outs() << "Unkown scev with type '" << scevTypesToString[baseScev->getSCEVType()] << "':\n";
                                    llvm::outs() << "\t" << *baseScev << "\n";
                                    HANDLE_UNKOWN_VALUE(phiNode);
                                }
                                current = llvm::cast<llvm::SCEVUnknown>(baseScev)->getValue();
                                continue;
                            }
                        }
                    }

                    // phiScev can still be loop variant, without being computable. 
                    // Someday i could look into this, but i have no idea right now how to get something from that
                }

                // fallback case
                for (auto& incomingVal : phiNode->incoming_values()) {
                    // llvm::outs() << "For phinode '" << *phiNode << "': Now analyzing incoming val: '" << *incomingVal.get() << "'\n";
                    llvm::Value* val = incomingVal.get();
                    auto valInBounds = isInBounds_internal<DIR>(val, offset, isInRange);
                    if (!valInBounds.inBounds)
                        return valInBounds;
                }
                return IsInBoundsResult::True();
            }
            assert(false);
        } else if (auto selectInst = llvm::dyn_cast<llvm::SelectInst>(current)) {
            // cannot be self-referential AFAIK
            for (uint i = 1; i < 3; i++) {
                auto val = selectInst->getOperand(i);
                auto valInBounds = isInBounds_internal<DIR>(val, offset, isInRange);
                if (!valInBounds.inBounds)
                    return valInBounds;
            }
            return IsInBoundsResult::True();
        } else if (auto inttoptr = llvm::dyn_cast<llvm::IntToPtrInst>(current)) {
            auto srcEl = inttoptr->getOperand(0);
            assert(dataLayout.getTypeSizeInBits(inttoptr->getType()) == dataLayout.getTypeSizeInBits(srcEl->getType()));
            current = srcEl;
        } else if (auto ptrtoint = llvm::dyn_cast<llvm::PtrToIntOperator>(current)) {
            auto srcEl = ptrtoint->getOperand(0);
            assert(dataLayout.getTypeSizeInBits(ptrtoint->getType()) == dataLayout.getTypeSizeInBits(srcEl->getType()));
            current = srcEl;
        } else if (auto binaryOp = llvm::dyn_cast<llvm::BinaryOperator>(current)) {
            assert(binaryOp->getNumOperands() == 2);
            auto lhs = binaryOp->getOperand(0);
            auto rhs = binaryOp->getOperand(1);

            auto& pointerDetector = MAM.getResult<PointerDetectionAnalysis>(module);
            // this has to be a pointer value, but not necessarily a confirmed one
            auto binOpTypes = pointerDetector.findBinaryOpValueTypes(binaryOp);

            if (binOpTypes.has_value()) {
                auto pointerOperand = binOpTypes->pointerOperand;
                auto nonPtrOperand = binOpTypes->nonPointerOperand;
                assert(pointerOperand);
                assert(nonPtrOperand);
                assert(!llvm::isa<llvm::ConstantInt>(pointerOperand));
                
                auto constantIntVal = [&] () -> std::optional<llvm::APInt> {
                    if (auto constInt = llvm::dyn_cast<llvm::ConstantInt>(nonPtrOperand)) 
                        return constInt->getValue();
                    assert(!llvm::isa<llvm::ConstantInt>(nonPtrOperand));

                    auto& funcscev = FAM.getResult<llvm::ScalarEvolutionAnalysis>(*binaryOp->getFunction());
                    auto nonPointerScev = funcscev.getSCEV(nonPtrOperand);
                    auto nonPtrRange = funcscev.getSignedRange(nonPointerScev);

                    if (nonPtrRange.isSingleElement())
                        return *nonPtrRange.getSingleElement();

                    if (DIR == LOWER && binaryOp->getOpcode() == llvm::BinaryOperator::Or)
                        return llvm::APInt::getNullValue(64);

                    if (DIR == UPPER && binaryOp->getOpcode() == llvm::BinaryOperator::And)
                        return llvm::APInt::getNullValue(64);

                    if (!getSignedSCEVLimit<DIR>(nonPointerScev, funcscev).has_value())
                        return std::nullopt;

                    if (DIR == UPPER) {
                        switch (binaryOp->getOpcode()) {
                            case llvm::BinaryOperator::Add:
                                return nonPtrRange.getSignedMax();
                            case llvm::BinaryOperator::Or: 
                                return nonPtrRange.getUnsignedMax();
                            case llvm::BinaryOperator::Sub:
                                return nonPtrRange.getSignedMin();
                            default:
                                HANDLE_UNKOWN_VALUE(binaryOp);
                        }
                    } else {
                        assert(DIR == LOWER);
                        switch (binaryOp->getOpcode()) {
                            case llvm::BinaryOperator::Add:
                                return nonPtrRange.getSignedMin();
                            case llvm::BinaryOperator::Sub:
                                return nonPtrRange.getSignedMax();
                            case llvm::BinaryOperator::And:
                                return nonPtrRange.getUnsignedMin();
                            default:
                                HANDLE_UNKOWN_VALUE(binaryOp);
                        }
                    }
                } ();

                if (constantIntVal.has_value()) {
                    switch (binaryOp->getOpcode()) {
                        case llvm::Instruction::BinaryOps::And: 
                        case llvm::Instruction::BinaryOps::Sub: {
                            offset -= constantIntVal.value();
                            current = pointerOperand;
                        } break;
                        case llvm::Instruction::BinaryOps::Or:
                        case llvm::Instruction::BinaryOps::Add: {
                            offset += constantIntVal.value();
                            current = pointerOperand;
                        } break;
                        default: 
                            HANDLE_UNKOWN_VALUE(binaryOp);
                    }
                } else return IsInBoundsResult::False("binop: non-constant offset");
            } else {
                // we couldn't figure out the binaryOp types. However, at least one of these guys is definitely a pointer
                // but there is nothing we can do here that we can't do in is_unconfirmed_pointer
                // this case probably totally includes things like (ptr & getpagesize())
                return IsInBoundsResult::False("binop: unanalyzable");;
            }
        } else if (auto constExpr = llvm::dyn_cast<llvm::ConstantExpr>(current)) {
            auto oldCurrent = current;
            auto newbase = constExpr->stripAndAccumulateConstantOffsets(dataLayout, offset, true);
            current = newbase;
            if (current == oldCurrent) {
                auto constExprAsInst = constExpr->getAsInstruction();
                auto result = isInBounds_internal<DIR>(constExprAsInst, offset, isInRange);
                assert(!boundsCache.count(constExprAsInst));
                assert(constExprAsInst->getNumUses() == 0);
                constExprAsInst->deleteValue();
                return result;
            }
            assert(current != oldCurrent);
        } else if (llvm::isa<llvm::Function>(current)) {
            // W^X and/or XOM will handle this case
            if(offset.sge(-((int64_t)UINT32_MAX)) && offset.sle(UINT32_MAX)) {
                return IsInBoundsResult::True();
            } else {
                assert(offset != 0);
                llvm::outs() << "Offset to function: " << offset << "\n";
                return IsInBoundsResult::False("func: large offset to code location");
            }
        } else if (auto freeze = llvm::dyn_cast<llvm::FreezeInst>(current)) {
            // if the below fires, i think we can assume it's a safe pointer
            ASSERT_ELSE_UNKOWN(!(llvm::isa<llvm::UndefValue, llvm::PoisonValue>(freeze->getOperand(0))), current);
            current = freeze->getOperand(0);
        } else {
            llvm::outs() << "Weird guy: \n";
            llvm::outs() << "\t" <<  *current << "\n";
            llvm::outs() << "Is an instruction: " << (llvm::isa<llvm::Instruction>(current) ? "yes" : "no") << ".\n";
            llvm::outs() << "Is a metadataval: " << (llvm::isa<llvm::MetadataAsValue>(current) ? "yes" : "no") << ".\n";
            llvm::outs() << "Is a constant int: " << (llvm::isa<llvm::ConstantInt>(current) ? "yes" : "no") << ".\n";
            // llvm::outs() << "Is a function arg: " << (llvm::isa<llvm::Argument>(current) ? "yes" : "no") << ".\n";
            llvm::outs().flush();
            llvm::outs() << "Arrived here via (oldest first):\n";
            uint i = 1;
            for (auto& passedVal : passedInstrs) {
                llvm::outs() << i << ": " << *passedVal.val << " (in '" << getFuncName(passedVal.val) << "')\n";
                i++;
            }

            assert(!"Unknown instruction!");
        }

        // this doesnt catch everything ('continue')
        assert(oldCurrent != current);
    }
    
    assert(!"Unreachable!");
}

IsInBoundsAnalysis::Result IsInBoundsAnalysis::run(llvm::Module &module, llvm::ModuleAnalysisManager &MAM) {
    return BoundsChecker(module, MAM);
}
