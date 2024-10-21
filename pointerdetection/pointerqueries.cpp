#include <llvm-utils/pointerdetection/pointerdetection.h>

#include <llvm-utils/util.h>
#include <llvm-utils/safetyanalysis/allocationbounds.h>

llvm::Value* PointerDetector::find_real_base(llvm::Value *arithmetic) const {
    static thread_local std::vector<const llvm::Value*> passedInstrs;
    const auto size = passedInstrs.size();
    run_on_destruct resetPassedInstrs([&](){
        assert(size <= passedInstrs.size());
        passedInstrs.erase(passedInstrs.begin() + size, passedInstrs.end());
    });

    if (llvm::is_contained(passedInstrs, arithmetic)) 
        return arithmetic;

    auto current = arithmetic;
    bool done = false;
    const auto& dataLayout = module.getDataLayout();

    while (!done) {
        assert(current);
        auto oldCurrent = current;
        passedInstrs.push_back(current);
        if (auto gepOperator = llvm::dyn_cast<llvm::GEPOperator>(current)) {
            current = gepOperator->getPointerOperand();
        } else if (auto binaryOp = llvm::dyn_cast<llvm::BinaryOperator>(current)) {
            auto binOpTypes = findBinaryOpValueTypes(binaryOp);
            if (!binOpTypes.has_value()) 
                done = true;
            else 
                current = binOpTypes->pointerOperand;
        } else if (auto bitcastOp = llvm::dyn_cast<llvm::BitCastOperator>(current)) {
            current = bitcastOp->getOperand(0);
        } else if (auto castInst = llvm::dyn_cast<llvm::CastInst>(current)) {
            switch (castInst->getOpcode()) {
                case llvm::Instruction::FPToSI: // fuck this
                case llvm::Instruction::FPToUI:
                case llvm::Instruction::SExt:
                case llvm::Instruction::ZExt:
                    ASSERT_ELSE_UNKOWN(dataLayout.getTypeSizeInBits(castInst->getType()) == 64, castInst);
                    done = true;
                    break;
                case llvm::Instruction::CastOps::IntToPtr:
                case llvm::Instruction::CastOps::PtrToInt:
                    assert(castInst->isNoopCast(dataLayout));
                [[fallthrough]];
                case llvm::Instruction::CastOps::BitCast: {
                    current = castInst->getOperand(0);
                } break;
                default: {
                    llvm::outs() << "passed instructions leading up:\n";
                    for (auto inst : passedInstrs)
                        llvm::outs() << "\t" << *inst << "\n";
                    HANDLE_UNKOWN_VALUE(castInst);
                }
            }
        } else if (auto phiNode = llvm::dyn_cast<llvm::PHINode>(current)) {
            auto& FAM = getFAM(module, MAM);
            auto& loopInfo = FAM.getResult<llvm::LoopAnalysis>(*phiNode->getFunction());
            auto& SCEV = FAM.getResult<llvm::ScalarEvolutionAnalysis>(*phiNode->getFunction());
            auto& domTree = FAM.getResult<llvm::DominatorTreeAnalysis>(*phiNode->getFunction());
            if (auto constVal = phiNode->hasConstantValue()) {
                if (!domTree.dominates(constVal, phiNode)) {
                    llvm::outs() << "phiNode: " << *phiNode << "\n";
                    llvm::outs() << "constPhi: " << *constVal << "\n";
                }
                assert(domTree.dominates(constVal, phiNode));
                current = constVal;
            } else if (auto baseSCEV = SCEV.getPointerBase(SCEV.getSCEV(phiNode)); llvm::isa<llvm::SCEVUnknown>(baseSCEV)) { 
                // simple loop-bound pointer iteration check
                // ive had `getPointerBase` fail for loop-bound pointers using ptrtoint ints (e.g. reverse_iterator)
                // so definitely keep the fallback case!
                auto base = llvm::cast<llvm::SCEVUnknown>(baseSCEV)->getValue();
                current = base;
            } else { // fallback case
                // as a last-ditch effort, we check if all incomingvalues happen to have the same commonbase
                //  if so, we can continue through it with the commonbase

                // first, find the first non-recursive phi
                //  all recursive incoming values may be ignored, they cyclically depend on this phiNode -> they are not the base
                llvm::Value* commonBase = nullptr;
                auto firstIt = llvm::find_if(phiNode->incoming_values(), [&] (llvm::Value* val) -> bool {
                    auto base = find_real_base(val);
                    if (base != val) {
                        commonBase = base;
                        return true;
                    }
                    return false;
                });

                // we've seen all phinode values before? that's impossible!
                ASSERT_ELSE_UNKOWN(firstIt != phiNode->incoming_values().end(), phiNode);
                assert(commonBase); // no way it's null here

                // continue with the rest of the incoming values and check whether they have the same commonbase
                for (auto it = firstIt + 1; it != phiNode->incoming_values().end(); it++) {
                    auto base = find_real_base(*it);
                    if (base != *it && base != commonBase) {
                        // not recursive but also not the same as what we found already
                        done = true;
                        break;
                    }
                }

                assert(!done);
                current = commonBase;
            }
        } else if (auto selectInst = llvm::dyn_cast<llvm::SelectInst>(current)) {
            auto baseIfTrue = find_real_base(selectInst->getTrueValue());
            auto baseIfFalse = find_real_base(selectInst->getFalseValue());

            // both options of the select are self-referential??
            //      maybe this is possible, idk
            ASSERT_ELSE_UNKOWN(
                baseIfTrue != selectInst->getTrueValue() 
                || baseIfFalse != selectInst->getFalseValue()
            , selectInst);

            if (baseIfTrue != selectInst->getTrueValue() && baseIfTrue == baseIfFalse) {
                // both of them are non-recursive and equal
                current = baseIfTrue;
            } else {
                done = true;
            }
        } else if (isNonWrapperAllocSite(current) 
                    || llvm::isa<llvm::ConstantPointerNull, llvm::UndefValue, llvm::LoadInst, llvm::ExtractValueInst,
                                llvm::ExtractElementInst, llvm::Argument, llvm::CallBase, llvm::PHINode, llvm::SelectInst>(current)
        ) {
            done = true;
        } else if (auto constantInt = llvm::dyn_cast<llvm::ConstantInt>(current)) {
            done = true;
        } else if (auto freeze = llvm::dyn_cast<llvm::FreezeInst>(current)) {
            // if the below fires, i think we can assume it's a safe pointer
            ASSERT_ELSE_UNKOWN(!(llvm::isa<llvm::UndefValue, llvm::PoisonValue>(freeze->getOperand(0))), current);
            current = freeze->getOperand(0);
        } else if (auto constExpr = llvm::dyn_cast<llvm::ConstantExpr>(current)) {
            switch (constExpr->getOpcode()) {
                case llvm::Instruction::IntToPtr:
                case llvm::Instruction::PtrToInt:
                    ASSERT_ELSE_UNKOWN(constExpr->getNumOperands() == 1, constExpr);
                    ASSERT_ELSE_UNKOWN(dataLayout.getTypeSizeInBits(constExpr->getOperand(0)->getType()) == 64, constExpr);
                    ASSERT_ELSE_UNKOWN(dataLayout.getTypeSizeInBits(constExpr->getType()) == 64, constExpr);
                    current = constExpr->getOperand(0);
                    break;
                default:
                    HANDLE_UNKOWN_VALUE(constExpr);
            }
        } else {
            HANDLE_UNKOWN_VALUE(current);
        }

        if (oldCurrent == current)
            assert(done);
    }

    return current;
}

llvm::Value* PointerDetector::strip_pointer_casts(llvm::Value *pointer) const {
    const auto& dataLayout = module.getDataLayout();

    while (true) {
        // ASSERT_ELSE_UNKOWN(is_confirmed_pointer(pointer), pointer);

        if (auto gep = llvm::dyn_cast<llvm::GEPOperator>(pointer)) {
            auto operand = gep->getPointerOperand();
            auto offset = findConstantOffset(gep);
            if (offset.has_value() && offset->isNullValue()) {
                pointer = operand;
            } else break;
        } else if (auto binaryOp = llvm::dyn_cast<llvm::BinaryOperator>(pointer)) {
            auto offset = findConstantOffset(binaryOp);
            if (offset.has_value() && offset->isNullValue()) {
                auto operandTypes = findBinaryOpValueTypes(binaryOp);
                assert(operandTypes.has_value());
                pointer = operandTypes->pointerOperand;
            } else break;
        } else if (auto castInst = llvm::dyn_cast<llvm::CastInst>(pointer)) {
            switch (castInst->getOpcode()) {
                case llvm::Instruction::CastOps::IntToPtr:
                case llvm::Instruction::CastOps::PtrToInt:
                    assert(castInst->isNoopCast(dataLayout));
                [[fallthrough]];
                case llvm::Instruction::CastOps::BitCast: {
                    pointer = castInst->getOperand(0);
                } break;
                default:
                    HANDLE_UNKOWN_VALUE(pointer);
            }
        } else if (auto bitcastOp = llvm::dyn_cast<llvm::BitCastOperator>(pointer)) {
            pointer = bitcastOp->getOperand(0);
        } else if (auto freeze = llvm::dyn_cast<llvm::FreezeInst>(pointer)) {
            assert((!llvm::isa<llvm::UndefValue, llvm::PoisonValue>(freeze->getOperand(0))));
            pointer = freeze->getOperand(0);
        } else if (llvm::isa<llvm::AllocaInst, llvm::GlobalVariable, llvm::ConstantPointerNull, llvm::ConstantInt, 
                                llvm::Function, llvm::LoadInst, llvm::ExtractElementInst, llvm::Argument, 
                                llvm::CallBase, llvm::PHINode, llvm::SelectInst>(pointer)
        ) {
            break;
        } else if (auto constExpr = llvm::dyn_cast<llvm::ConstantExpr>(pointer)) {
            auto inst = constExpr->getAsInstruction();
            auto ret = strip_pointer_casts(inst);
            inst->deleteValue();
            return ret;
        } else HANDLE_UNKOWN_VALUE(pointer);
    }
    return pointer;
}

std::optional<llvm::APInt> PointerDetector::findConstantOffset(llvm::GEPOperator* gep) const {
    llvm::APInt offset(64, 0);
    if (gep->hasAllConstantIndices()) {
        for (auto& idxuse : gep->indices())
            assert(llvm::isa<llvm::ConstantInt>(idxuse.get()));
        bool val = gep->accumulateConstantOffset(module.getDataLayout(), offset);
        assert(val);
        return offset;
    } else if (auto gepInst = llvm::dyn_cast<llvm::GetElementPtrInst>(gep)) {
        auto& scev = getFAM(module, MAM).getResult<llvm::ScalarEvolutionAnalysis>(*gepInst->getFunction());
        auto gepScev = scev.getSCEV(gepInst);
        auto offsetScev = scev.getMinusSCEV(gepScev,scev.getSCEV(gepInst->getPointerOperand()));
        auto range = scev.getSignedRange(offsetScev);
        if (auto single = range.getSingleElement())
            return {*single};
        return std::nullopt;
    } else HANDLE_UNKOWN_VALUE(gep);
}

std::optional<llvm::APInt> PointerDetector::findConstantOffset(llvm::BinaryOperator* binaryOp) const {
    if (binaryOp->getOpcode() != llvm::Instruction::Add || binaryOp->getOpcode() != llvm::Instruction::Sub)
        return std::nullopt;

    bool isAdd = binaryOp->getOpcode() == llvm::Instruction::Add;
    if (!isAdd) {
        if (binaryOp->getOpcode() != llvm::Instruction::Sub)
            return std::nullopt;
        assert(binaryOp->getOpcode() == llvm::Instruction::Sub);
    }

    auto& dataLayout = module.getDataLayout();
    llvm::APInt offset(64, 0);

    assert(binaryOp->getNumOperands() == 2);
    auto lhs = binaryOp->getOperand(0);
    auto rhs = binaryOp->getOperand(1);

    // this has to be a pointer value, but not necessarily a confirmed one
    auto bValTypes = findBinaryOpValueTypes(binaryOp);

    if (bValTypes.has_value()) {
        if (auto constInt = llvm::dyn_cast<llvm::ConstantInt>(bValTypes->nonPointerOperand)) {
            if (isAdd)
                return constInt->getValue();
            else 
                return -constInt->getValue();
        } else {
            auto& scev = getFAM(module, MAM).getResult<llvm::ScalarEvolutionAnalysis>(*binaryOp->getFunction());
            if (auto single = scev.getSignedRange(scev.getSCEV(bValTypes->nonPointerOperand)).getSingleElement())
                return *single;
            else return std::nullopt;
        }
    }

    return std::nullopt;
}
