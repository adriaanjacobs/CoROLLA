#include "pass.h"
#include "util.h"
#include <cstdint>
#include <optional>
#include <llvm/Analysis/ScalarEvolutionExpressions.h>
#include <llvm/Analysis/Delinearization.h>

llvm::AnalysisKey OffsetFinderAnalysis::Key;

/*
    Using
    llvm::getPointersDiff(Type *ElemTyA, Value *PtrA, Type *ElemTyB,  Value *PtrB, const DataLayout &DL, ScalarEvolution &SE, bool StrictCheck, bool CheckType);
    I can verify/benchmark this implementation.
    I have to figure out SCEV then though
*/

std::optional<llvm::APInt> OffsetFinder::find_offset(llvm::Value* offsetPtr, llvm::Value* const basePtr){
    static thread_local std::vector<const llvm::Value*> passedInstrs;
    const auto size = passedInstrs.size();
    // llvm::outs() << rand() << ": Called findoffset (nested level: " << size << ")\n";
    run_on_destruct resetPassedInstrs([&](){
        assert(size <= passedInstrs.size());
        passedInstrs.erase(passedInstrs.begin() + size, passedInstrs.end());
        assert(passedInstrs.size() == size);
    });

    auto& dataLayout = module.getDataLayout();
    auto& context = module.getContext();
    auto& FAM = getFAM(module, MAM);

    llvm::Value* current = offsetPtr;
    llvm::APInt offset(64, 0, false);

    while (current != basePtr) {
        // current = current->stripPointerCasts();
        passedInstrs.push_back(current);
        if (AllocWrapperDetector::isStaticAllocationSite(current)) {
            // these are other (static) allocations, likely also in the points-to set of this pointer operand. We can easily compute  
            // the offset to that allocation at this point, but we know (current != allocInstr) that this is not the allocation we are concerned about, 
            // so it makes no sense
            return {};
            assert(false);
        } else if (llvm::isa<llvm::ConstantPointerNull>(current) 
                    || llvm::isa<llvm::ConstantInt>(current)
        ){
            // these are not allocation sites, but do provide a constant value to the pointer
            // should i make a pass that replaces the undefvalues with nullptrs?
            ASSERT_ELSE_UNKOWN(llvm::isa<llvm::ConstantPointerNull>(current) || (llvm::isa<llvm::ConstantInt>(current) && llvm::cast<llvm::ConstantInt>(current)->isZero()), current);
            return std::nullopt;
            assert(false);
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
                bool success = llvm::getIndexExpressionsFromGEP(funcScev,gepInstr, subscripts, sizes);
                if (!success)
                    return std::nullopt;
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
                    auto val = funcScev.getSignedRangeMax(scev);
                    assert(val.sge(funcScev.getSignedRangeMin(scev)));
                    // heuristic to filter out the uncomputable ones
                    if (scev->getSCEVType() != llvm::scCouldNotCompute && val.slt(llvm::APInt::getSignedMaxValue(64))) {
                        constantIndices.push_back(llvm::ConstantInt::get(context, val));
                        assert(constantIndices.size() <= subscripts.size());
                    } else {
                        break;
                    }
                }

                if (constantIndices.size() == subscripts.size()) {
                    auto dummyGep = llvm::GetElementPtrInst::Create(gepInstr->getSourceElementType(), gepInstr->getPointerOperand(), constantIndices);
                    assert(dummyGep->hasAllConstantIndices());
                    llvm::APInt offsetBefore = offset;
                    bool val = dummyGep->accumulateConstantOffset(dataLayout, offset);
                    assert(val);
                    if (offset == offsetBefore) {
                        for (auto& idx : dummyGep->indices()) {
                            assert(llvm::isa<llvm::ConstantInt>(idx.get()));
                            if(!llvm::cast<llvm::ConstantInt>(idx.get())->equalsInt(0)) {
                                llvm::outs() << "dummyGep: " << *dummyGep << "\n";
                                llvm::outs() << "realGep: " << *gepInstr << "\n";
                                assert(false);
                            }
                        }
                    }
                    current = dummyGep->getPointerOperand();
                    dummyGep->deleteValue();
                    continue;
                } else {
                    assert(constantIndices.size() < subscripts.size());
                    return std::nullopt;
                }
                assert(false);
            }
            assert(false);
        } else if (llvm::isa<llvm::LoadInst, llvm::ExtractValueInst, llvm::UndefValue>(current)) {
            // treat undefvalues as loadinsts (value cannot be determined)
            // to keep following LoadInsts i would need to alias analyze the operand here
            // that's not a problem, but then it spawns a whole tree of possibilities to check
            return std::nullopt;
            assert(false);
        } else if (llvm::isa<llvm::BitCastInst>(current) || llvm::isa<llvm::ZExtInst>(current)) {
            auto castInst = llvm::dyn_cast<llvm::CastInst>(current);
            assert(castInst);
            assert(castInst->getNumOperands() == 1);
            current = castInst->getOperand(0);
            continue;
            assert(false);
        } else if (llvm::isa<llvm::PHINode>(current) || llvm::isa<llvm::SelectInst>(current)) {
            // I am not so sure if this is supposed to have this many gains: only if their traversal somehow
            // does not lead us to find other allocations in the points-to set (both branches are dominated by the same block at some point)
            auto phiNode = llvm::dyn_cast<llvm::PHINode>(current);
            auto selectInst = llvm::dyn_cast<llvm::SelectInst>(current);
            assert(phiNode || selectInst);

            std::optional<llvm::APInt> rec_offset;
            if (phiNode) {
                if (auto constVal = phiNode->hasConstantValue()) {
                    current = constVal;
                    continue;
                } else {
                    for (auto& incomingVal : phiNode->incoming_values()) {
                        // llvm::outs() << "For phinode '" << *phiNode << "': Now analyzing incoming val: '" << *incomingVal.get() << "'\n";
                        llvm::Value* val = incomingVal.get();
                        // Facking heuristic because nginx has some big ass functions and i dont have enough stack space
                        if (!llvm::is_contained(passedInstrs, val) && passedInstrs.size() < 1000) {
                            if (auto valInstr = llvm::dyn_cast<llvm::Instruction>(val))
                                assert(valInstr->getFunction() == phiNode->getFunction());
                            auto proposed_offset = find_offset(val, basePtr);
                            if (proposed_offset.has_value()) {
                                if (!rec_offset.has_value() || proposed_offset->ugt(*rec_offset))
                                    rec_offset = proposed_offset;
                            } else { // all offsets must be constant to prune this
                                break;
                            }
                        } else {
                            // i dont know how to handle data flow loops.
                            // by ignoring, rec_offset will remain nullopt 
                        }
                    }
                }
            } else {
                assert(selectInst);

                for (uint i = 0; i < 2; i++) {
                    llvm::Value* val = selectInst->getOperand(i + 1);
                    if (!llvm::is_contained(passedInstrs, val)) {
                        auto proposed_offset = find_offset(val, basePtr);
                        if (proposed_offset.has_value()) {
                            if (!rec_offset.has_value() || proposed_offset->ugt(*rec_offset))
                                rec_offset = proposed_offset;
                        } else { // all offsets must be constant to prune this
                            break;
                        }
                    } else {
                        // i dont know how to handle data flow loops.
                        // assert(!"Select instructions are not supposed to create traversal loops right?");
                        // apparently they are hahaha
                    }
                }
            }

            if (!rec_offset.has_value()) {
                // there is no compile time offset found
                return std::nullopt;
            } else {
                // assert(false);
                offset += *rec_offset;
                return offset;
            }
            assert(false);
        } else if (auto constExpr = llvm::dyn_cast<llvm::ConstantExpr>(current)) {
            // size_t off_before = offset.getLimitedValue();
            auto off_before = offset;
            constExpr->stripAndAccumulateConstantOffsets(dataLayout, offset, true);
            llvm::APInt constantOffset = offset - off_before;
            // if (!constantOffset.isNullValue())
            //     llvm::outs() << "Calculated constant offset here: " << constantOffset << "\n";
            return offset;
            assert(false);
        } else if (auto inttoptr = llvm::dyn_cast<llvm::IntToPtrInst>(current)) {
            if (inttoptr->isNoopCast(dataLayout)) {
                // for inttoptr, the implementation of `isNoopCast` does what we want here
                current = inttoptr->getOperand(0);
                continue;
            } else {
                return std::nullopt;
            }
            assert(false);
        } else if (auto binaryOp = llvm::dyn_cast<llvm::BinaryOperator>(current)) {
            assert(binaryOp->getNumOperands() == 2);
            auto constantOperand = llvm::dyn_cast<llvm::Constant>(binaryOp->getOperand(llvm::isa<llvm::Constant>(binaryOp->getOperand(1))));
            std::optional<llvm::APInt> constantIntVal;
            if (constantOperand) {
                auto constantInt = llvm::dyn_cast<llvm::ConstantInt>(constantOperand);
                assert(constantInt);
                auto nonConstOperand = binaryOp->getOperand(!llvm::isa<llvm::Constant>(binaryOp->getOperand(1)));
                assert(!llvm::isa<llvm::Constant>(nonConstOperand));
                
                switch (binaryOp->getOpcode()) {
                    case llvm::Instruction::BinaryOps::And: {
                        // probably some stuff to do here but can't be bothered
                        return std::nullopt;
                    } break;
                    case llvm::Instruction::BinaryOps::Or:
                        // or's flip bits, can never reset bits
                        // so worst case scenario, every bit that is set in the or will be set in the result and no other bits are changed
                        // then, the offset == the mask, so we treat this like an Add!
                    case llvm::Instruction::BinaryOps::Add: {
                        offset += constantInt->getValue();
                        current = nonConstOperand;
                        continue;
                    } break;
                    default: 
                        HANDLE_UNKOWN_VALUE(binaryOp);
                }
                assert(false);
            } else if (binaryOp->getOpcode() == llvm::Instruction::BinaryOps::Add){
                auto& funcScev = FAM.getResult<llvm::ScalarEvolutionAnalysis>(*binaryOp->getFunction());
                std::optional<llvm::APInt> pot_offset;
                for (uint i = 0; i < binaryOp->getNumOperands(); i++) {
                    auto offsetOperand = binaryOp->getOperand(i);
                    auto pointerOperand = binaryOp->getOperand(!i);
                    assert(offsetOperand != pointerOperand);
                    auto scev = funcScev.getSCEV(offsetOperand);
                    auto constantIntVal = funcScev.getSignedRangeMax(scev);
                    assert(constantIntVal.sge(funcScev.getSignedRangeMin(scev)));
                    // heuristic to filter out the uncomputable ones
                    if (scev->getSCEVType() == llvm::scCouldNotCompute && constantIntVal.slt(llvm::APInt::getSignedMaxValue(64))) {
                        auto operandOffset = find_offset(pointerOperand, basePtr);
                        if (operandOffset.has_value()) {
                            *operandOffset += constantIntVal;
                            if (!pot_offset.has_value() || pot_offset->ult(*operandOffset))
                                pot_offset = operandOffset;
                        }
                    }
                }
                

                if (pot_offset.has_value()) {
                    llvm::outs() << "Found scevved constant offset to add binaryop: " << *pot_offset << "\n";
                    return offset + *pot_offset;
                } else {
                    return std::nullopt;
                }
            } else {
                return std::nullopt;
            }
            assert(false);
        } else if (llvm::isa<llvm::CallBase>(current)) {
            // no interprocedural analysis
            // maybe i can model some common ones here though?
            // malloc etc are not included here since that will already have been handled by the earlier isBuiltInAllocationSite()
            return std::nullopt;
            assert(false);
        } else if (auto argument = llvm::dyn_cast<llvm::Argument>(current)) {
            // we are intraprocedural, stop here
            return std::nullopt;
            assert(false);
        } else if (auto icmpInst = llvm::dyn_cast<llvm::ICmpInst>(current)) {
            // no idea why we would ever hit this but spec gcc does and defining
            // an offset from a boolean to some base allocation makes no sense
            return std::nullopt;
            assert(false);
        } else {
            llvm::outs() << "Weird guy: \n";
            llvm::outs() << *current << "\n";
            llvm::outs() << "Is an instruction: " << (llvm::isa<llvm::Instruction>(current) ? "yes" : "no") << ".\n";
            llvm::outs() << "Is a metadataval: " << (llvm::isa<llvm::MetadataAsValue>(current) ? "yes" : "no") << ".\n";
            llvm::outs() << "Is a constant int: " << (llvm::isa<llvm::ConstantInt>(current) ? "yes" : "no") << ".\n";
            // llvm::outs() << "Is a function arg: " << (llvm::isa<llvm::Argument>(current) ? "yes" : "no") << ".\n";
            llvm::outs().flush();
            assert(!"Unknown instruction!");
            return std::nullopt;
            assert(false);
        }
    }
    
    return offset;
    // assert(!"Unreachable!!");
}


bool OffsetFinder::flowFromXtoAnyY(llvm::Value* X, llvm::ArrayRef<llvm::Value*> Ys) {
    for (auto y : Ys) {
        auto offset = find_offset(y, X);
        // debatable: we could relax the NullValue requirement here
        // but I'm scared that will explode the number of allocation
        // wrappers that we find
        if (offset.has_value() && offset->isNullValue())
            return true;
    }
    return false;
}

OffsetFinderAnalysis::Result OffsetFinderAnalysis::run(llvm::Module& module, llvm::AnalysisManager<llvm::Module>& MAM) {
    return OffsetFinder{module, MAM};
}