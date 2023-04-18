#include "pass.h"
#include <util.h>
#include <pointerdetection/pointerdetection.h>
#include <reachability/reachingdefinitions.h>

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
        llvm::outs() << "\t#" << rank << ": " << maxIt->getFirst() << ". " << maxIt->getSecond() << " occurrences.\n";
        rank++;
        bailStats.erase(maxIt);
    }
    bailStats = statsCpy;
}

bool BoundsChecker::isInBounds(llvm::Value* offsetPtr, llvm::APInt storeSize) {
    auto [ptrIt, ptrInserted] = boundsCache.try_emplace(offsetPtr);
    assert(ptrIt != boundsCache.end());
    auto [offsetIt, offsetInserted] = ptrIt->getSecond().try_emplace(storeSize, std::nullopt);
    assert(offsetIt != ptrIt->getSecond().end());
    auto& allocDetector = MAM.getResult<AllocWrapperAnalysis>(module);

    auto isInRange = [&] (llvm::Value* current, llvm::APInt offset, DIRECTION) -> std::optional<bool> {
        if (allocDetector.isBuiltInAllocationSite(current)) {
            // these are other allocations, likely also in the points-to set of this pointer operand. 
            auto allocSize = allocDetector.findMinimumAllocSize(current);

            if (!allocSize.has_value()) 
                allocSize = llvm::APInt{64, 0};
            
            bool ret = offset.sge(0) && offset.sle(allocSize.value());
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
        bool inBounds = isInBounds_internal<UPPER>(offsetPtr, storeSize, isInRange) && isInBounds_internal<LOWER>(offsetPtr, llvm::APInt{64,0}, isInRange);
        // if (!inBounds && llvm::isa<llvm::Constant>(MAM.getResult<PointerDetectionAnalysis>(module).strip_pointer_casts(offsetPtr))) {
        //     BREAKPOINT();
        //     volatile bool debugInBoundsUpper = isInBounds_internal<UPPER>(offsetPtr, storeSize, isInRange);
        //     volatile bool debugInBoundsLower = isInBounds_internal<LOWER>(offsetPtr, llvm::APInt{64,0}, isInRange);
        //     llvm::outs() << "upper: " << debugInBoundsUpper << ", lower: " << debugInBoundsLower << "\n";
        // }

        if (!inBounds)
            bailStats[allocDetector.getValueDescription(mostRecentDecider)]++;
        offsetIt->getSecond() = inBounds;
    }
    assert(offsetIt->getSecond().has_value());
    return offsetIt->getSecond().value();
}

std::optional<bool> BoundsChecker::isInCache(llvm::Value* offsetPtr, llvm::APInt offset) const {
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
    return isInBounds_internal<UPPER>(offsetPtr, offset, isInRange, false) && isInBounds_internal<LOWER>(offsetPtr, offset, isInRange, false);
}

template<DIRECTION DIR>
bool BoundsChecker::isInBounds_internal(llvm::Value* offsetPtr, llvm::APInt offset, const std::function<std::optional<bool>(llvm::Value*, llvm::APInt, DIRECTION)>& isInRange, bool checkTheCache) {
    struct PassedValue {
        llvm::Value* val;
        llvm::APInt offset;
    };
    static thread_local std::vector<PassedValue> passedInstrs;
    const auto size = passedInstrs.size();
    // llvm::outs() << rand() << ": Called findoffset (nested level: " << size << ")\n";
    run_on_destruct resetPassedInstrs([&](){
        assert(passedInstrs.size() >= 1);
        this->mostRecentDecider = passedInstrs.back().val;
        assert(size <= passedInstrs.size());
        passedInstrs.erase(passedInstrs.begin() + size, passedInstrs.end());
        assert(passedInstrs.size() == size);
    });

    auto& dataLayout = module.getDataLayout();
    auto& context = module.getContext();
    auto& allocDetector = MAM.getResult<AllocWrapperAnalysis>(module);
    auto& FAM = getFAM(module, MAM);

    llvm::Value* current = offsetPtr;

    while (true) {
        // check if we've seen this one before
        auto passedValIt = llvm::find_if(passedInstrs, [&] (const PassedValue& passedVal) -> bool {
            return passedVal.val == current;
        });
        if (passedValIt != passedInstrs.end()) {
            if (passedValIt->offset == offset)
                return true; // dataflow back to myself with no offset difference? safe
            else
                return false; // may change offset indefinitely
        }

        auto oldCurrent = current;
        passedInstrs.push_back({current, offset});

        if (checkTheCache)
            if (auto val = isInCache(current, offset))
                return val.value();

        if (auto retVal = isInRange(current, offset, DIR)) {
            assert(retVal.has_value());
            return retVal.value();
        } else if (llvm::isa<llvm::ConstantPointerNull, llvm::ConstantInt>(current)) {
            if (auto constInt = llvm::dyn_cast<llvm::ConstantInt>(current))
                offset += constInt->getValue();
            llvm::ConstantRange userspace({64, 8'388'608U}, {64, UINT64_MAX >> 17});
            if (userspace.contains(offset)) {
                // llvm::outs() << "Offset to NULL: " << offset << "\n";
                return false;
            }
            return true; // the program will crash when dereferencing these anyway
        } else if (auto argument = llvm::dyn_cast<llvm::Argument>(current)) {
            auto function = argument->getParent();
            // if (!function->hasInternalLinkage())
            //     return false;

            auto& pointerDetector = MAM.getResult<PointerDetectionAnalysis>(module); 
            llvm::DenseSet<llvm::Value*> incomingVals;
            bool isComplete = pointerDetector.getIncomingValuesForArgument(argument, incomingVals);
            if (!isComplete)
                return false;
            for (auto argOperand : incomingVals) {
                assert(argOperand->getType() == argument->getType());
                if (!isInBounds_internal<DIR>(argOperand, offset, isInRange)) 
                    return false;
            }
            return true;
        } else if (auto callInst = llvm::dyn_cast<llvm::CallBase>(current)) {
            if (auto calledFunc = callInst->getCalledFunction()) {
                if (calledFunc->isDeclaration()) {
                    // if it was an allocation function, we would've found it by now
                    // maybe i can still model some common ones here?
                    return false;
                }
                // check if all return values happen to be in bounds, if so we gucci
                for (auto& bb : *calledFunc) {
                    if (auto retInst = llvm::dyn_cast<llvm::ReturnInst>(bb.getTerminator())) {
                        auto retVal = retInst->getReturnValue();
                        if (!isInBounds_internal<DIR>(retVal, offset, isInRange))
                            return false;
                    }
                }
                return true;
            } // else indirect call, can't look through those :/. Maybe do a pointer analysis here?
            return false;
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
                    return false;
                assert(success);
                llvm::SmallVector<llvm::Value*> constantIndices;

                ASSERT_ELSE_UNKOWN(subscripts.size() == sizes.size() || subscripts.size() == sizes.size() + 1, gepInstr);
                ASSERT_ELSE_UNKOWN(subscripts.size() == gepInstr->getNumIndices() || subscripts.size() == gepInstr->getNumIndices() - 1, gepInstr);

                if (subscripts.size() == gepInstr->getNumIndices() - 1) {
                    auto scev = funcScev.getSCEV(gepInstr->getOperand(1));
                    assert(llvm::isa<llvm::SCEVConstant>(scev) && llvm::cast<llvm::SCEVConstant>(scev)->getValue()->isZero());
                    subscripts.insert(subscripts.begin(), scev);
                    assert(subscripts.size() >= 2);
                    assert(*subscripts.begin() == scev);
                }

                for (auto scev : subscripts) {
                    // TODO: fix this, not entirely accurate (lower/negative bound might be more dangerous than upper bound)
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
                    return false;
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
            if (auto definingPtr = rds.findDefForLoad(loadInst)) {
                return isInBounds_internal<DIR>(definingPtr, offset, isInRange);
            }
            return false;

            auto defOrClobberIsInBounds = [this, offset, isInRange] (const llvm::MemDepResult& localDep) -> bool {
                auto defInst = localDep.getInst();
                assert(defInst && (localDep.isDef() || localDep.isClobber()));

                llvm::Value* storedVal = nullptr;
                if (auto storeInst = llvm::dyn_cast<llvm::StoreInst>(defInst)) {
                    storedVal = storeInst->getValueOperand();
                } else if (auto cmpxchg = llvm::dyn_cast<llvm::AtomicCmpXchgInst>(defInst)) {
                    storedVal = cmpxchg->getNewValOperand();
                } else if (auto atomicrmw = llvm::dyn_cast<llvm::AtomicRMWInst>(defInst)) {
                    switch (atomicrmw->getOperation()) {
                        case llvm::AtomicRMWInst::FAdd:
                        case llvm::AtomicRMWInst::FSub:
                        case llvm::AtomicRMWInst::Sub:
                        case llvm::AtomicRMWInst::And:
                        case llvm::AtomicRMWInst::Nand:
                        case llvm::AtomicRMWInst::Or:
                        case llvm::AtomicRMWInst::Xor: {
                            HANDLE_UNKOWN_VALUE(atomicrmw);
                        } break;
                        case llvm::AtomicRMWInst::Add: {
                            // all of these arithmetic ones represent a computation on the stored value
                            // + re-storing the value. Essentially, this is a store + valueOperand is 
                            // arithmetic, encoded into a single instruction
                            // but since I don't know what the old stored value is, the best I can do is
                            // a memdepanalysis on the pointeroperand here to figure that out.
                            // i'm already doing a memdepanalysis on the pointeroperand though
                            // idk
                            return false;
                        } break;
                        case llvm::AtomicRMWInst::Max:
                        case llvm::AtomicRMWInst::Min:
                        case llvm::AtomicRMWInst::UMax:
                        case llvm::AtomicRMWInst::UMin:
                        case llvm::AtomicRMWInst::Xchg: {
                            storedVal = atomicrmw->getValOperand();
                        } break;
                        default:
                            HANDLE_UNKOWN_VALUE(atomicrmw);
                    }
                }

                if (storedVal) {
                    if (module.getDataLayout().getTypeSizeInBits(storedVal->getType()) != 64)
                        return false;
                    
                    auto& pointerDetector = MAM.getResult<PointerDetectionAnalysis>(module);
                    auto status = pointerDetector.is_unconfirmed_pointer(storedVal);
                    
                    // this is definitely not ideal/complete but I can't deal with it anymore right now
                    if (status.has_value()) {
                        if (status != PointerDetector::POINTER) {
                            // 64-bit stores of non-pointers to a potentially clobbering location definitely don't clobber
                            // However, they may store to an unaligned location and partially clobber the value
                            // Hence: FIXME
                            return true;
                        } else return isInBounds_internal<DIR>(storedVal, offset, isInRange);
                    } else return false;
                    assert(false);
                } else if (auto callInst = llvm::dyn_cast<llvm::CallBase>(defInst)) {
                    // probably means the defInst is an argument to the call
                    // easy case: the function does not write that memory at all
                    // hard case: it does
                    // to handle this, i should run the memdepanalysis on the called function
                    // and then figure out what the clobbers are at exit nodes of the function
                    // not sure if memdepanalysis supports that kind of thing?

                    // a quick and easy fix is to run the function argument attribute inferrer up front
                    // then check the argument attributes
                    return false;
                } else if (llvm::isa<llvm::AllocaInst>(defInst)) {
                    // would be undefvalue. By using safeinit i could mark these as 
                    // 0 and then get gains
                    return false;
                } else {
                    HANDLE_UNKOWN_VALUE(defInst);
                }
            };
            
            auto& memdep = FAM.getResult<llvm::MemoryDependenceAnalysis>(*loadInst->getFunction());
            auto& domTree = FAM.getResult<llvm::DominatorTreeAnalysis>(*loadInst->getFunction());

            // FIXME: For loadinsts, i should probably look for a localDep in the same basic block/in all blocks it post-dominates?
            // because memdepanalysis for some reason thinks i give a shit about loads
            // maybe i should check first if basic blocks can get reported twice though, that would indicate
            // that memdepanalysis knows whats up

            auto localDep = memdep.getDependency(loadInst);
            if (!(localDep.isDef() || localDep.isClobber()) || llvm::isa<llvm::LoadInst>(localDep.getInst())) {
                llvm::SmallVector<llvm::NonLocalDepResult> nonLocalDeps;
                memdep.getNonLocalPointerDependency(loadInst, nonLocalDeps);
                if (nonLocalDeps.empty()) {
                    // from my little investigation, this means that this loads directly from something like an argument, without intervening store
                    // there may be something to do here similar to callInsts in defOrClobberIsInBounds. but for now frick it
                    return false;
                }
                assert(!nonLocalDeps.empty());
                bool allInBounds = true;
                for (auto& nonLocalDep : nonLocalDeps) {
                    assert(allInBounds);
                    auto& depresult = nonLocalDep.getResult();
                    assert(!depresult.isNonLocal());

                    auto defInst = depresult.getInst();

                    if (!defInst) {
                        // pretty weird case tbh, only nonfunclocal possible?
                        assert(depresult.isNonFuncLocal() || depresult.isUnknown());
                        // assert(nonLocalDeps.size() == 1);
                        allInBounds = false;
                    } else if (!llvm::isa<llvm::LoadInst>(defInst)) {
                        allInBounds = defOrClobberIsInBounds(depresult);
                    } // else (loadinst) do nothing. but it really shouldnt contain a loadinst tbh
                       
                    if (!allInBounds)
                        break;
                }

                return allInBounds;
            } else {
                return defOrClobberIsInBounds(localDep);
            }
            assert(false);
        } else if (auto extractValue = llvm::dyn_cast<llvm::ExtractValueInst>(current)) {
            auto& rds = MAM.getResult<ReachingDefinitionsAnalysis>(module);
            auto defs = rds.findDefsForExtractValue(extractValue);
            if (defs.empty())
                return false;

            for (auto def : defs)
                if (!isInBounds_internal<DIR>(def, offset, isInRange))
                    return false;
            return true;
        } else if (llvm::isa<llvm::UndefValue, llvm::ExtractElementInst>(current)) {
            return false;
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
            return false;
        } else if (auto phiNode = llvm::dyn_cast<llvm::PHINode>(current)) {
            if (auto constVal = phiNode->hasConstantValue()) {
                current = constVal;
                continue;
            } else {
                auto& loopInfo = FAM.getResult<llvm::LoopAnalysis>(*phiNode->getFunction());
                auto& funcscev = FAM.getResult<llvm::ScalarEvolutionAnalysis>(*phiNode->getFunction());
                auto phiScev = funcscev.getSCEV(phiNode);
                assert(phiScev);
                if (auto loop = loopInfo.getLoopFor(phiNode->getParent())) {
                    if (funcscev.hasComputableLoopEvolution(phiScev, loop)) {
                        assert(phiScev->getSCEVType() != llvm::scCouldNotCompute);
                        auto baseScev = funcscev.getPointerBase(phiScev);
                        assert(baseScev);
                        assert(baseScev->getSCEVType() != llvm::scCouldNotCompute);
                        assert(baseScev->getSCEVType() == llvm::scUnknown);
                        auto offsetScev = funcscev.getMinusSCEV(phiScev, baseScev);
                        assert(offsetScev && offsetScev->getSCEVType() != llvm::scCouldNotCompute);
                        auto offsetVal = getSignedSCEVLimit<DIR>(offsetScev, funcscev);
                        // there's an implicit assumption here that the pointer evolves via add's through the loop
                        // maybe we can validate this somehow by checking the scevtype of "phiScev"
                        // but I think this is guaranteed by the loopevolution definition
                        if (offsetVal.has_value()) {
                            offset += offsetVal.value();
                            assert(llvm::isa<llvm::SCEVUnknown>(baseScev));
                            current = llvm::cast<llvm::SCEVUnknown>(baseScev)->getValue();
                            continue;
                        }
                    }

                    // phiScev can still be loop variant, without being computable. 
                    // Someday i could look into this, but i have no idea right now how to get something from that
                }

                // fallback case
                bool allInBounds = true;
                for (auto& incomingVal : phiNode->incoming_values()) {
                    // llvm::outs() << "For phinode '" << *phiNode << "': Now analyzing incoming val: '" << *incomingVal.get() << "'\n";
                    llvm::Value* val = incomingVal.get();
                    allInBounds = allInBounds && isInBounds_internal<DIR>(val, offset, isInRange);
                }
                return allInBounds;
            }
            assert(false);
        } else if (auto selectInst = llvm::dyn_cast<llvm::SelectInst>(current)) {
            // cannot be self-referential AFAIK
            return isInBounds_internal<DIR>(selectInst->getTrueValue(), offset, isInRange) && isInBounds_internal<DIR>(selectInst->getFalseValue(), offset, isInRange);
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
                } else return false;
            } else {
                // we couldn't figure out the binaryOp types. However, at least one of these guys is definitely a pointer
                // but there is nothing we can do here that we can't do in is_unconfirmed_pointer
                // this case probably totally includes things like (ptr & getpagesize())
                return false;
            }
        } else if (auto constExpr = llvm::dyn_cast<llvm::ConstantExpr>(current)) {
            auto oldCurrent = current;
            auto newbase = constExpr->stripAndAccumulateConstantOffsets(dataLayout, offset, true);
            current = newbase;
            if (current == oldCurrent) {
                switch(constExpr->getOpcode()) {
                    case llvm::Instruction::IntToPtr: {
                        auto srcEl = constExpr->getOperand(0);
                        assert(dataLayout.getTypeSizeInBits(constExpr->getType()) == dataLayout.getTypeSizeInBits(srcEl->getType()));
                        current = srcEl;
                    } break;
                    default:
                        HANDLE_UNKOWN_VALUE(constExpr);
                }
            }
            assert(current != oldCurrent);
        } else if (llvm::isa<llvm::Function>(current)) {
            // W^X and/or XOM will handle this case
            if(offset.sge(-((int64_t)UINT32_MAX)) && offset.sle(UINT32_MAX)) {
                return true;
            } else {
                assert(offset != 0);
                llvm::outs() << "Offset to function: " << offset << "\n";
                return false;
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
