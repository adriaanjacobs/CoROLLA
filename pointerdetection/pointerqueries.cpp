#include <llvm-utils/pointerdetection/pointerdetection.h>

#include <llvm-utils/util.h>
#include <llvm-utils/safetyanalysis/allocationbounds.h>

#include <llvm/Analysis/ValueTracking.h>

// simple loop-bound pointer iteration check
// returns null if unsuccessful (i.e. it did nothing)
llvm::Value* findLoopBoundPHIBase(llvm::PHINode* phi, llvm::ScalarEvolution& SCEV) {
    // ive had `getPointerBase` fail for loop-bound pointers using ptrtoint ints (e.g. reverse_iterator)
    // so definitely keep the fallback case!
    auto baseSCEV = SCEV.getPointerBase(SCEV.getSCEV(phi));
    auto baseUnknownSCEV = llvm::dyn_cast<llvm::SCEVUnknown>(baseSCEV);
    if (!baseUnknownSCEV)
        return nullptr;

    auto base = baseUnknownSCEV->getValue();
    if (base == phi) // otherwise we did nothing, e.g., if the phi was not loop-bound
        return nullptr;

    return base;
}

std::pair<llvm::Value*, bool> PointerDetector::find_real_base(llvm::Value *arithmetic) const {
    static thread_local std::vector<const llvm::Value*> passedInstrs;
    const auto size = passedInstrs.size();
    run_on_destruct resetPassedInstrs([&](){
        assert(size <= passedInstrs.size());
        passedInstrs.erase(passedInstrs.begin() + size, passedInstrs.end());
    });

    if (llvm::is_contained(passedInstrs, arithmetic)) 
        return {arithmetic, false}; // compared to the value we entered with, this wasn't offseted

    auto current = arithmetic;
    bool done = false;
    const auto& dataLayout = module.getDataLayout();
    bool offseted = false;

    while (!done) {
        assert(current);
        auto oldCurrent = current;
        passedInstrs.push_back(current);

        if (auto it = pointerToRealBase.find(current); it != pointerToRealBase.end()) {
            auto [cachedBase, cachedBaseOffseted] = it->getSecond();
            return {cachedBase, cachedBaseOffseted || offseted};
        }

        // this ensures that all subsequent operations probably modify the pointer
        current = strip_pointer_casts(current);

        if (auto gepOperator = llvm::dyn_cast<llvm::GEPOperator>(current)) {
            current = gepOperator->getPointerOperand();
            offseted = true;
        } else if (auto binaryOp = llvm::dyn_cast<llvm::BinaryOperator>(current)) {
            auto binOpTypes = findBinaryOpValueTypes(binaryOp);
            if (!binOpTypes.has_value()) 
                done = true;
            else {
                current = binOpTypes->pointerOperand;
                offseted = true;
            }
        } else if (auto phiNode = llvm::dyn_cast<llvm::PHINode>(current)) {
            auto& FAM = getFAM(module, MAM);
            auto& loopInfo = FAM.getResult<llvm::LoopAnalysis>(*phiNode->getFunction());
            auto& SCEV = FAM.getResult<llvm::ScalarEvolutionAnalysis>(*phiNode->getFunction());
            auto& domTree = FAM.getResult<llvm::DominatorTreeAnalysis>(*phiNode->getFunction());
            ASSERT_ELSE_UNKOWN(!phiNode->hasConstantValue(), phiNode); // or strip_pointer_casts wouldve caught it
            if (auto loopBoundPHIBase = findLoopBoundPHIBase(phiNode, SCEV)) {
                ASSERT_ELSE_UNKOWN(current != loopBoundPHIBase, current);
                current = loopBoundPHIBase;
                offseted = true; // assume some loop-bound phi is always offseted
            } else { // fallback case
                // as a last-ditch effort, we check if all incomingvalues happen to have the same commonbase
                //  if so, we can continue through it with the commonbase

                // first, find the first non-recursive phi
                //  all recursive incoming values may be ignored, they cyclically depend on this phiNode -> they are not the base
                llvm::Value* commonBase = nullptr;
                auto firstIt = llvm::find_if(phiNode->incoming_values(), [&] (llvm::Value* val) -> bool {
                    auto [base, baseOffseted] = find_real_base(val);
                    if (base != phiNode) {
                        commonBase = base;
                        return true;
                    }
                    return false;
                });

                // we've seen all phinode values before? that's impossible!
                ASSERT_ELSE_UNKOWN(firstIt != phiNode->incoming_values().end(), phiNode);
                assert(commonBase); // no way it's null here

                // continue with the rest of the incoming values and check whether they have the same commonbase
                bool commonBaseOffseted = offseted;
                for (auto it = firstIt + 1; it != phiNode->incoming_values().end(); it++) {
                    auto [base, baseOffseted] = find_real_base(*it);
                    if (baseOffseted)
                        commonBaseOffseted = true;
                    if (base != commonBase) {
                        // not recursive but also not the same as what we found already
                        //  turned out to be necessary for SPEC06 perlbench (of course)
                        done = true;
                        pointerToRealBase[current] = {current, false}; // was a tough one to compute
                        break;
                    }
                }

                if (!done) {
                    ASSERT_ELSE_UNKOWN(current != commonBase, current);
                    // was very tough to compute, and very unlikely too. Def keep track of this
                    pointerToRealBase[current] = {commonBase, commonBaseOffseted};
                    current = commonBase;
                    offseted = commonBaseOffseted;
                }
            }
        } else if (auto selectInst = llvm::dyn_cast<llvm::SelectInst>(current)) {
            auto [baseIfTrue, ifTrueOffseted] = find_real_base(selectInst->getTrueValue());
            auto [baseIfFalse, ifFalseOffseted] = find_real_base(selectInst->getFalseValue());

            ASSERT_ELSE_UNKOWN(baseIfTrue != selectInst && baseIfFalse != selectInst, selectInst);

            if (baseIfTrue == baseIfFalse) {
                ASSERT_ELSE_UNKOWN(current != baseIfTrue, current);
                pointerToRealBase[current] = {baseIfTrue, ifTrueOffseted || ifFalseOffseted};
                current = baseIfTrue;
                offseted = offseted || ifTrueOffseted || ifFalseOffseted;
            } else {
                // we gotta stop, we can't find a common base
                done = true;
                pointerToRealBase[current] = {current, false};
            }
        } else if (isNonWrapperAllocSite(current) 
                    || llvm::isa<llvm::ConstantPointerNull, llvm::UndefValue, llvm::LoadInst, llvm::ExtractValueInst,
                                llvm::ExtractElementInst, llvm::Argument, llvm::CallBase, llvm::PHINode, llvm::SelectInst>(current)
        ) {
            done = true;
        } else if (auto constantInt = llvm::dyn_cast<llvm::ConstantInt>(current)) {
            done = true;
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
        } else if (auto function = llvm::dyn_cast<llvm::Function>(current)) {
            // I know it's cursed, but CMake's "is symbol defined" sample programs do load from function addresses
            done = true;
        } else {
            HANDLE_UNKOWN_VALUE(current);
        }

        if (oldCurrent == current)
            ASSERT_ELSE_UNKOWN(done, current);
    }

    assert(done);

    return {current, offseted};
}

llvm::Value* PointerDetector::strip_pointer_casts(llvm::Value *pointer) const {
    const auto& dataLayout = module.getDataLayout();

    while (true) {
        if (auto gep = llvm::dyn_cast<llvm::GEPOperator>(pointer)) {
            auto operand = gep->getPointerOperand();
            auto offset = findConstantOffset(gep);
            if (offset.has_value() && offset->isZero()) {
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
                case llvm::Instruction::FPToSI: // fuck this
                case llvm::Instruction::FPToUI:
                case llvm::Instruction::SExt:
                case llvm::Instruction::ZExt:
                    ASSERT_ELSE_UNKOWN(dataLayout.getTypeSizeInBits(castInst->getType()) == 64, castInst);
                    return pointer;
                case llvm::Instruction::IntToPtr:
                case llvm::Instruction::PtrToInt:
                    assert(castInst->isNoopCast(dataLayout));
                [[fallthrough]];
                case llvm::Instruction::BitCast: {
                    pointer = castInst->getOperand(0);
                } break;
                case llvm::Instruction::Trunc: {
                    // i found just one case of this, in SPEC17's x264_s on an AVX-512 machine
                    //  we check for this specific case, since we'd have to manually vet others
                    auto i512Val = llvm::dyn_cast<llvm::BitCastOperator>(castInst->getOperand(0));
                    ASSERT_ELSE_UNKOWN(i512Val && dataLayout.getTypeSizeInBits(i512Val->getType()) == 512, castInst);
                    auto vectorOf8 = llvm::dyn_cast<llvm::ConstantVector>(i512Val->getOperand(0));
                    ASSERT_ELSE_UNKOWN(vectorOf8 && vectorOf8->getNumOperands() == 8, castInst); // 8-element vector
                    auto extractedElement = dataLayout.isLittleEndian() ? vectorOf8->getOperand(0) : vectorOf8->getOperand(vectorOf8->getNumOperands() - 1);
                    ASSERT_ELSE_UNKOWN(dataLayout.getTypeSizeInBits(extractedElement->getType()) == 64, castInst);
                    pointer = extractedElement;
                } break;
                default: {
                    HANDLE_UNKOWN_VALUE(castInst);
                }
            }
        } else if (auto bitcastOp = llvm::dyn_cast<llvm::BitCastOperator>(pointer)) {
            pointer = bitcastOp->getOperand(0);
        } else if (auto freeze = llvm::dyn_cast<llvm::FreezeInst>(pointer)) {
            // if the below fires, i think we can assume it's a safe pointer
            ASSERT_ELSE_UNKOWN(!(llvm::isa<llvm::UndefValue, llvm::PoisonValue>(freeze->getOperand(0))), pointer);
            pointer = freeze->getOperand(0);
        } else if (auto phi = llvm::dyn_cast<llvm::PHINode>(pointer)) {
            if (auto constVal = phi->hasConstantValue()) {
                ASSERT_ELSE_UNKOWN(pointer != constVal, pointer);
                pointer = constVal;
            } else break;
        } else if (llvm::isa<llvm::AllocaInst, llvm::GlobalVariable, llvm::ConstantPointerNull, llvm::ConstantInt, 
                                llvm::Function, llvm::LoadInst, llvm::ExtractElementInst, llvm::ExtractValueInst, llvm::Argument, 
                                llvm::CallBase, llvm::SelectInst, llvm::UndefValue>(pointer)
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
    if (gep->hasAllConstantIndices()) {
        llvm::APInt offset{64, 0};
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

llvm::Value* PointerDetector::find_simple_base_pointer(llvm::Value* val) {
    if (auto gep = llvm::dyn_cast<llvm::GEPOperator>(val)) {
        return find_simple_base_pointer(gep->getPointerOperand());
    } else if (auto binaryOp = llvm::dyn_cast<llvm::BinaryOperator>(val)) {
        ASSERT_ELSE_UNKOWN(!llvm::isa<llvm::Constant>(binaryOp->getOperand(0)) 
                        || !llvm::isa<llvm::Constant>(binaryOp->getOperand(1)), 
        val);

        if (llvm::isa<llvm::Constant>(binaryOp->getOperand(0)))
            return find_simple_base_pointer(binaryOp->getOperand(1));
        else if (llvm::isa<llvm::Constant>(binaryOp->getOperand(1)))
            return find_simple_base_pointer(binaryOp->getOperand(0));

        // give up, we don't know which side of the binaryOp is the ptr
        return binaryOp;
    } else if (auto castInst = llvm::dyn_cast<llvm::CastInst>(val)) {
        auto& dataLayout = castInst->getModule()->getDataLayout();
        ASSERT_ELSE_UNKOWN(dataLayout.getTypeSizeInBits(castInst->getDestTy()) == 64, castInst); // otherwise bug
        if (dataLayout.getTypeSizeInBits(castInst->getSrcTy()) != 64)
            return castInst;
        return find_simple_base_pointer(castInst->getOperand(0));
    } else if (auto freeze = llvm::dyn_cast<llvm::FreezeInst>(val)) {
        return find_simple_base_pointer(freeze->getOperand(0));
    } else if (llvm::isa<llvm::PtrToIntOperator, llvm::BitCastOperator>(val)) {
        return find_simple_base_pointer(llvm::cast<llvm::Operator>(val)->getOperand(0));
    } else if (auto intToPtr = llvm::dyn_cast<llvm::IntToPtrInst>(val)) {
        return find_simple_base_pointer(intToPtr->getOperand(0));
    } else if (llvm::isa<llvm::PHINode, llvm::LoadInst, llvm::CallBase, llvm::SelectInst, llvm::Argument, llvm::ExtractValueInst, llvm::ExtractElementInst, llvm::AllocaInst, llvm::Constant>(val)) {
        // sources
        return val;
    } else {
        HANDLE_UNKOWN_VALUE(val);
    }
}
