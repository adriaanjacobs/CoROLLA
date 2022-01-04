#include <util.h>
#include "mpk_instrument/pass.h"
#include "pointerdetection.h"
#include "wrapgeps/wrapgeps.h"

#include <bit>
#include <bitset>

#include <cstdint>
#include <array>
#include <experimental/array>
#include <optional>

llvm::AnalysisKey PointerDetectionAnalysis::Key;

void PointerDetector::identify_start_pointers(llvm::Module& module) {
    // Initialize with all known pointers
    auto& dataLayout = module.getDataLayout();
    for (auto& global : module.globals()) {
        mark_value(dataLayout, &global, POINTER);
    }
    for (auto& func : module) {
        for (auto& bb : func) {
            for (auto& inst : bb) {
                if (isAllocationCall(&inst))
                    mark_value(dataLayout, &inst, POINTER);

                if (inst.mayReadOrWriteMemory()) {
                    auto pointerOperand = llvm::getLoadStorePointerOperand(&inst);
                    if (pointerOperand) {
                        assert(pointerOperand->getType()->isPointerTy());
                        mark_value(dataLayout, pointerOperand, POINTER);
                    } else if (auto cmpxchgInst = llvm::dyn_cast<llvm::AtomicCmpXchgInst>(&inst)) {
                        mark_value(dataLayout, cmpxchgInst->getPointerOperand(), POINTER);
                    } else if (auto atomicrmwInst = llvm::dyn_cast<llvm::AtomicRMWInst>(&inst)) {
                        mark_value(dataLayout, atomicrmwInst->getPointerOperand(), POINTER);
                    } else if (auto callInst = llvm::dyn_cast<llvm::CallBase>(&inst)) {
                        for (uint i = 0; i < callInst->getNumArgOperands(); i++) {
                            if (callInst->paramHasAttr(i, llvm::Attribute::Dereferenceable)) {
                                mark_value(dataLayout, callInst->getArgOperand(i), POINTER);
                            }
                        }
                    } else if (llvm::isa<llvm::FenceInst>(&inst)) {
                        // ignore, the actual memory accesses have already been put into the pipeline here
                    } else {
                        HANDLE_UNKOWN_VALUE(&inst);
                    }
                }

                bool canBeNull = false;
                bool canBeFreed = false;
                if (inst.getPointerDereferenceableBytes(module.getDataLayout(), canBeNull, canBeFreed) > 0) {
                    // print
                }
            }
        }
    }

    llvm::outs() << pointers.size() << " start pointers identified.\n";
}

llvm::Value* PointerDetector::strip_pointer_casts(llvm::Value *pointer) {
    const auto& dataLayout = module.getDataLayout();
    auto& boundsChecker = MAM.getResult<IsInBoundsAnalysis>(module);

    while (true) {
        // ASSERT_ELSE_UNKOWN(is_confirmed_pointer(pointer), pointer);

        if (auto gep = llvm::dyn_cast<llvm::GEPOperator>(pointer)) {
            auto operand = gep->getPointerOperand();
            auto offset = boundsChecker.findConstantOffset(gep);
            if (offset.has_value() && offset->isNullValue()) {
                pointer = operand;
            } else break;
        } else if (auto binaryOp = llvm::dyn_cast<llvm::BinaryOperator>(pointer)) {
            auto offset = boundsChecker.findConstantOffset(binaryOp);
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
                case llvm::Instruction::CastOps::BitCast: {
                    pointer = castInst->getOperand(0);
                } break;
                default:
                    HANDLE_UNKOWN_VALUE(pointer);
            }
        } else if (auto bitcastOp = llvm::dyn_cast<llvm::BitCastOperator>(pointer)) {
            pointer = bitcastOp->getOperand(0);
        } else if (AllocWrapperDetector::isStaticAllocationSite(pointer) || GepDetector::isaSafePointerSourceType(pointer)
                    || llvm::isa<llvm::ConstantPointerNull, llvm::ConstantInt>(pointer)
        ) {
            break;
        } else HANDLE_UNKOWN_VALUE(pointer);
    }
    return pointer;
}

void PointerDetector::mark_actual_vs_formal_args(llvm::Module& module) {
    struct ArgDesc {
        bool isPointer;
        size_t count;
    };

    struct FuncDesc {
        size_t invocations = 0;
        llvm::SmallVector<ArgDesc> argDescs;
        bool retIsPointer = false;
        size_t pointerCalls = 0;
    };

    auto& dataLayout = module.getDataLayout();
    llvm::DenseMap<llvm::Function*, FuncDesc> funcToDescs;

    // record information about the function definition
    for (auto& func : module) {
        auto result = funcToDescs.insert({&func, {}});
        assert(result.second);
        auto& funcDesc = result.first->getSecond();
        
        funcDesc.retIsPointer = [&] {
            if (func.getReturnType()->isVoidTy() || func.isDeclaration() || func.getName() == "main")
                return false;
            
            size_t returns = 0;
            for (auto& bb : func) {
                if (auto retInst = llvm::dyn_cast<llvm::ReturnInst>(bb.getTerminator())) {
                    if (!is_confirmed_pointer(retInst->getReturnValue()))
                        return false;
                    returns++;
                }
            }

            if (returns == 0 && dataLayout.getTypeSizeInBits(func.getReturnType()) == 32) {
                return false;
            }
            ASSERT_ELSE_UNKOWN(returns > 0, &func);
            return true;
        } ();

        for (auto& arg : func.args()) {
            funcDesc.argDescs.push_back({is_confirmed_pointer(&arg), 0});
        }
    }

    // record information about the function invocations
    for (auto& func : module) {
        for (auto& bb : func) {
            for (auto& inst : bb) {
                if (auto callInst = llvm::dyn_cast<llvm::CallBase>(&inst)) {
                    auto calledFunc = callInst->getCalledFunction();
                    if (calledFunc) {
                        auto& funcDesc = funcToDescs[calledFunc];
                        funcDesc.invocations++;
                        size_t declaredArgCount = calledFunc->arg_size();
                        assert(declaredArgCount <= callInst->getNumArgOperands());
                        for (uint i = 0; i < declaredArgCount; i++) {
                            auto arg = callInst->getArgOperand(i);
                            if (funcDesc.argDescs[i].isPointer) {
                                mark_value(dataLayout, arg, POINTER);
                            } else {
                                funcDesc.argDescs[i].count += is_confirmed_pointer(arg);
                            }
                        }

                        if (funcDesc.retIsPointer) {
                            assert(!callInst->getType()->isVoidTy());
                            mark_value(dataLayout, callInst, POINTER);
                        } else {
                            funcDesc.pointerCalls += is_confirmed_pointer(callInst);
                        }
                    }
                }
            }
        }
    }

    for (auto& func : module) {
        auto& funcDesc = funcToDescs[&func];

        // if, for all invocations of this function, a specific argument is used as a pointer, the argument must be a pointer when used inside this function as well
        for (uint i = 0; i < func.arg_size(); i++) {
            if (funcDesc.argDescs[i].count == funcDesc.invocations && funcDesc.invocations != 0)
                mark_value(dataLayout, func.getArg(i), POINTER);
        }

        // if all invocations of this function are used as pointer values, all return values in this functions must be pointers
        if (funcDesc.pointerCalls == funcDesc.invocations && funcDesc.invocations != 0) {
            for (auto& bb : func) {
                assert(!func.getReturnType()->isVoidTy());
                if (auto retInst = llvm::dyn_cast<llvm::ReturnInst>(bb.getTerminator())) {
                    mark_value(dataLayout, retInst->getReturnValue(), POINTER);
                }
            }
        }
    }
}

/*
    This is sound but not (necessarily) complete 
    because there are places where we cannot be sure that something is a pointer.
    
    Example 1: load X, X++, store X
        This can totally be a pointer we're loading & storing here, but we cannot know for sure (unless PTA)
    Example 2: ptr = x binaryOp y
        If both x and y just got loaded from memory/are not used in clear ways, we know that one of them
        should be a pointer, but we never know which one

    BTW, not all pointer modifications are top-level: atomicrmw 
*/
PointerDetector::Detector(llvm::Module& module, llvm::ModuleAnalysisManager &MAM) :
    module{module}, MAM{MAM}
{
    identify_start_pointers(module);

    llvm::DenseSet<llvm::Value*> cpy;
    size_t it_no = 0;

    while (cpy.size() != pointers.size()) {
        llvm::outs() << "Running iteration number " << it_no << "...\n";

        mark_actual_vs_formal_args(module);
        llvm::outs() << "\tApplied formal<->actual func arg taint. " << pointers.size() << " total pointers identified. \n";

        cpy = pointers;
        for (auto pointer : cpy) {
            mark_pointer_origins(module.getDataLayout(), pointer);
        }
        llvm::outs() << "\tGot backwards markings. " << pointers.size() << " total pointers identified. \n";

        for (auto pointer : cpy) {
            mark_pointer_uses(module.getDataLayout(), pointer);
        }
        llvm::outs() << "\tGot forwards markings. " << pointers.size() << " total pointers identified. \n";

        it_no++;
    }

    // probabilistic sanity check for soundness
    for (auto ptr : pointers)
        ASSERT_ELSE_UNKOWN(module.getDataLayout().getTypeSizeInBits(ptr->getType()) == 64, ptr);

    // for (auto ptr : pointers) {
    //     if (auto gepInst = llvm::dyn_cast<llvm::GetElementPtrInst>(ptr)) {
    //         assert(is_confirmed_pointer(gepInst->getPointerOperand()));
    //     } else if (auto gepOperator = llvm::dyn_cast<llvm::GEPOperator>(ptr)) {
    //         assert(is_confirmed_pointer(gepOperator->getPointerOperand()));
    //     }
    // }
    
    llvm::outs() << pointers.size() << " pointers identified.\n";
}

void PointerDetector::mark_value(const llvm::DataLayout& dataLayout, llvm::Value* val, ValueType status) {
    switch (status) {
        case POINTER: {
            if (auto addInst = llvm::dyn_cast<llvm::AddOperator>(val)) {
                if (addInst->getNumUses() == 1) {
                    auto use = addInst->getSingleUndroppableUse();
                    if (llvm::isa<llvm::StoreInst>(use->getUser()) && use->getOperandNo() == 0 && (!is_confirmed_pointer(val))) {
                        HANDLE_UNKOWN_VALUE(val);
                    }
                }
            }
            ASSERT_ELSE_UNKOWN(dataLayout.getTypeSizeInBits(val->getType()) == 64, val);
            pointers.insert(val);
        } break;
        case INTEGER: { /* nothing for now */ } break;
        case NEGATED_POINTER: { negatedPointers.insert(val); } break;
        default: assert(false);
    }
}

// I think we look through pointer casts here, but it's not a problem since we're marking them during
// mark_pointer_origins later I think.
void PointerDetector::mark_pointer_uses(const llvm::DataLayout& dataLayout, llvm::Value* pointer) {
    for (auto& use : pointer->uses()) {
        auto const user = use.getUser();
        if (is_confirmed_pointer(user))
            continue;

        if (llvm::isa<llvm::StoreInst>(user) 
            || llvm::isa<llvm::ICmpInst>(user) 
            || llvm::isa<llvm::AtomicCmpXchgInst>(user) 
            || llvm::isa<llvm::AtomicRMWInst>(user)
            // || llvm::isa<llvm::GlobalVariable>(user)
            || llvm::isa<llvm::ConstantAggregate>(user)
            || llvm::isa<llvm::ReturnInst>(user)
        ) {

        } else if (auto switchInst = llvm::dyn_cast<llvm::SwitchInst>(user)) {
            assert(switchInst->getCondition() == use.get());
        } else if (auto callInst = llvm::dyn_cast<llvm::CallBase>(user)) {
            auto argOperand = use.get();
            assert(pointer == argOperand);
        } else {
            auto userStatus = is_unconfirmed_pointer(dataLayout, user);
            if (userStatus.has_value()) {
                if (userStatus == POINTER) {
                    ASSERT_ELSE_UNKOWN(dataLayout.getTypeSizeInBits(user->getType()) == 64, user);
                }
                mark_value(dataLayout, user, userStatus.value());
            }
        }
    }
}

void PointerDetector::mark_pointer_origins(const llvm::DataLayout& dataLayout, llvm::Value* pointer) {
    auto& FAM = getFAM(module, MAM);

    llvm::Value* current = pointer;
    mark_value(dataLayout, current, POINTER);
    bool done = false;
    while (!done) {
        llvm::SmallVector<std::pair<llvm::Value*, ValueType>> toMark;
        auto oldCurrent = current;
        assert(is_confirmed_pointer(current));
        if (auto gepInst = llvm::dyn_cast<llvm::GetElementPtrInst>(current)) {
            current = gepInst->getPointerOperand();
            toMark.push_back({current, POINTER});
        } else if (auto gepOperator = llvm::dyn_cast<llvm::GEPOperator>(current)) {
            current = gepOperator->getPointerOperand();
            toMark.push_back({current, POINTER});
        } else if (auto castInst = llvm::dyn_cast<llvm::CastInst>(current)) {
            auto destSize = dataLayout.getTypeSizeInBits(castInst->getDestTy());
            if (destSize == 32) {
                done = true;
                break;
            }
            ASSERT_ELSE_UNKOWN(dataLayout.getTypeSizeInBits(castInst->getSrcTy()) == destSize, castInst);
            current = castInst->getOperand(0);
            toMark.push_back({current, POINTER});
        } else if (auto bitcastOp = llvm::dyn_cast<llvm::BitCastOperator>(current)) {
            current = bitcastOp->getOperand(0);
            toMark.push_back({current, POINTER});
        } else if (auto ptrtointOp = llvm::dyn_cast<llvm::PtrToIntOperator>(current)) {
            current = ptrtointOp->getPointerOperand();
            toMark.push_back({current, POINTER});
        } else if (auto loadInst = llvm::dyn_cast<llvm::LoadInst>(current)) {
            done = true;
            break;
        } else if (auto binaryOp = llvm::dyn_cast<llvm::BinaryOperator>(current)) {
            {
                assert(is_confirmed_pointer(binaryOp));
            }
            auto lhs = binaryOp->getOperand(0);
            auto rhs = binaryOp->getOperand(1);

            auto lhStatus = is_unconfirmed_pointer(dataLayout, lhs);
            auto rhStatus = is_unconfirmed_pointer(dataLayout, rhs);

            if (!lhStatus.has_value() && !rhStatus.has_value()) {
                // TODO: maybe check these cases manually because we're losing info here
                done = true;
                break;
            }

            switch (binaryOp->getOpcode()) {
                case llvm::BinaryOperator::LShr:
                case llvm::BinaryOperator::Shl: {
                    // same as below, except int << ptr is INVALID
                    // only ptr << int is valid essentially
                    if (lhStatus.has_value())
                        assert(lhStatus == POINTER);
                    if (rhStatus.has_value())
                        assert(rhStatus == INTEGER);
                } [[fallthrough]];
                case llvm::BinaryOperator::Or:
                case llvm::BinaryOperator::Add:
                    // only `ptr + int` and `int + ptr` are valid
                case llvm::BinaryOperator::And: {
                    // since this HAS to return a pointer, the only valid possibilities are
                    // `ptr & int` or `int & ptr` and the ints HAVE to be base masks, not offset masks

                    if (lhStatus.has_value()) {
                        if (lhStatus == POINTER) {
                            assert(!rhStatus.has_value() || rhStatus == INTEGER);
                            toMark.push_back({lhs, POINTER});
                            toMark.push_back({rhs, INTEGER});
                            current = lhs;
                        } else {
                            assert(lhStatus == INTEGER); 
                            assert(!rhStatus.has_value() || rhStatus == POINTER);
                            toMark.push_back({lhs, INTEGER});
                            toMark.push_back({rhs, POINTER});
                            current = rhs;
                        }
                    } else {
                        assert(rhStatus.has_value());
                        if (rhStatus == POINTER) {
                            assert(!lhStatus.has_value() || lhStatus == INTEGER);
                            toMark.push_back({rhs, POINTER});
                            toMark.push_back({lhs, INTEGER});
                            current = rhs;
                        } else {
                            assert(rhStatus == INTEGER); 
                            assert(!lhStatus.has_value() || lhStatus == POINTER);
                            toMark.push_back({rhs, INTEGER});
                            toMark.push_back({lhs, POINTER});
                            current = lhs;
                        }
                    }
                } break;
                case llvm::BinaryOperator::Sub: {
                    // only `ptr - int` and `int - neg_ptr` are valid

                    if (lhStatus.has_value()) {
                        if (lhStatus == POINTER) {
                            assert(!rhStatus.has_value() || rhStatus == INTEGER);
                            toMark.push_back({lhs, POINTER});
                            toMark.push_back({rhs, INTEGER});
                            current = lhs;
                        } else {
                            assert(lhStatus == INTEGER);
                            assert(!rhStatus.has_value() || rhStatus == NEGATED_POINTER);
                            toMark.push_back({lhs, INTEGER});
                            toMark.push_back({rhs, NEGATED_POINTER});
                            done = true;
                        }
                    } else {
                        assert(rhStatus.has_value());
                        if (rhStatus == INTEGER) {
                            assert(!lhStatus.has_value() || lhStatus == POINTER);
                            toMark.push_back({lhs, POINTER});
                            toMark.push_back({rhs, INTEGER});
                            current = lhs;
                        } else {
                            assert(rhStatus == NEGATED_POINTER);
                            assert(!lhStatus.has_value() || lhStatus == INTEGER);
                            toMark.push_back({lhs, INTEGER});
                            toMark.push_back({rhs, NEGATED_POINTER});
                            done = true;
                        }
                    }
                } break;
                case llvm::Instruction::Mul: {
                    assert(lhStatus.has_value() || rhStatus.has_value());
                    if ((!rhStatus.has_value() || rhStatus == INTEGER)) {
                        ASSERT_ELSE_UNKOWN(llvm::isa<llvm::ConstantInt>(rhs) && llvm::cast<llvm::ConstantInt>(rhs)->getValue() == -1, binaryOp);
                        toMark.push_back({lhs, NEGATED_POINTER});
                        toMark.push_back({rhs, INTEGER});
                        done = true;
                    } else HANDLE_UNKOWN_VALUE(binaryOp);

                    // if (lhStatus.has_value()) {
                    //     ASSERT_ELSE_UNKOWN(!rhStatus.has_value() || rhStatus == INTEGER, binaryOp);
                    //     toMark.push_back({lhs, lhStatus.value()});
                    //     toMark.push_back({rhs, INTEGER});
                    //     if (lhStatus == POINTER)
                    //         current = lhs;
                    //     else done = true;
                    // } else {
                    //     assert(rhStatus.has_value());
                    //     ASSERT_ELSE_UNKOWN(!lhStatus.has_value() || lhStatus == INTEGER, binaryOp);
                    //     toMark.push_back({rhs, rhStatus.value()});
                    //     toMark.push_back({lhs, INTEGER});
                    // }
                } break;
                default: {
                    HANDLE_UNKOWN_VALUE(current);
                }
            }
        } else if (auto phiNode = llvm::dyn_cast<llvm::PHINode>(current)) {
            // `current` is, unconditionally, a confirmed pointer which is used for memory access etc.
            assert(is_confirmed_pointer(current));
            // so, all sides of this phiNode need to be confirmed pointers too
            for (auto& incomingUse : phiNode->incoming_values()) {
                assert(incomingUse.getUser() == phiNode);
                auto incomingVal = incomingUse.get();
                toMark.push_back({incomingVal, POINTER});
            }
            done = true;
            break;
        } else if (auto selectInst = llvm::dyn_cast<llvm::SelectInst>(current)) {
            // same reasoning as phiNode
            assert(selectInst->getNumOperands() == 3);
            for (uint i = 1; i < selectInst->getNumOperands(); i++) {
                llvm::Value* val = selectInst->getOperand(i);
                toMark.push_back({val, POINTER});
            }
            done = true;
            break;
        } else if (AllocWrapperDetector::isStaticAllocationSite(current)
                    || llvm::isa<llvm::CallBase>(current)
                    || llvm::isa<llvm::Argument>(current)
                    || llvm::isa<llvm::ConstantAggregate>(current)
                    || llvm::isa<llvm::ConstantPointerNull>(current)
                    || llvm::isa<llvm::ExtractElementInst>(current)
                    || llvm::isa<llvm::ExtractValueInst>(current)
                    || llvm::isa<llvm::UndefValue>(current)
        ) {
            done = true;
            break;
        } else if (llvm::isa<llvm::ReturnInst>(current)){
            assert(is_confirmed_pointer(current));
            done = true;
            break;
        } else {
            HANDLE_UNKOWN_VALUE(current);
        }

        ASSERT_ELSE_UNKOWN(done || oldCurrent != current, current);

        assert(!llvm::isa<llvm::Argument>(oldCurrent));
        auto func = functionOf(oldCurrent);
        if (func) {
            auto oldInst = llvm::cast<llvm::Instruction>(oldCurrent);
            auto& postDomTree = FAM.getResult<llvm::PostDominatorTreeAnalysis>(*func);
            auto oldNode = postDomTree.getNode(oldInst->getParent());
            auto curNode = postDomTree.getNode(llvm::isa<llvm::Instruction>(current) ? llvm::cast<llvm::Instruction>(current)->getParent() : &func->getEntryBlock());
            if (postDomTree.dominates(oldNode, curNode)) {
                for (auto mark : toMark)
                    mark_value(dataLayout, mark.first, mark.second);
            } else done = true;
        }
    }

    assert(done);
}

std::optional<PointerDetector::ValueType> PointerDetector::is_unconfirmed_pointer(const llvm::DataLayout& dataLayout, llvm::Value* current) const {
    static thread_local std::vector<const llvm::Value*> passedInstrs;
    const auto size = passedInstrs.size();
    // llvm::outs() << rand() << ": Called findoffset (nested level: " << size << ")\n";
    run_on_destruct resetPassedInstrs([&](){
        assert(size <= passedInstrs.size());
        passedInstrs.erase(passedInstrs.begin() + size, passedInstrs.end());
    });

    auto& FAM = getFAM(module, MAM);

    while (!is_confirmed_pointer(current)) {
        auto oldCurrent = current;
        passedInstrs.push_back(current);

        if (dataLayout.getTypeSizeInBits(current->getType()) <= 32)
            return INTEGER;

        if (llvm::isa<llvm::PtrToIntOperator>(current) || llvm::isa<llvm::IntToPtrInst>(current)) {
            auto srcTy = llvm::cast<llvm::User>(current)->getOperand(0)->getType();
            auto destTy = current->getType();
            ASSERT_ELSE_UNKOWN(dataLayout.getTypeSizeInBits(srcTy) == 64, current);
            if (dataLayout.getTypeSizeInBits(destTy) == 32)
                return INTEGER;
            ASSERT_ELSE_UNKOWN(dataLayout.getTypeSizeInBits(destTy) == dataLayout.getTypeSizeInBits(srcTy), current);
            current = llvm::cast<llvm::User>(current)->getOperand(0);
        } else if (llvm::isa<llvm::ZExtInst>(current) 
                    || llvm::isa<llvm::SExtInst>(current) 
                    || llvm::isa<llvm::TruncInst>(current) 
                    || llvm::isa<llvm::BitCastOperator>(current)
        ){
            current = llvm::cast<llvm::User>(current)->getOperand(0);
        } else if (llvm::isa<llvm::ConstantInt>(current) || llvm::isa<llvm::ConstantPointerNull>(current) || llvm::isa<llvm::UndefValue>(current)) {
            // treat constant pointers like integers: they are not (yet) used as pointer
            // they may be promoted later based on context information
            return INTEGER;
        } else if (llvm::isa<llvm::ICmpInst>(current)) { // used in f.e. ptr += (a == 0);
            // example: nginx: ngx_http_log_escape
            return INTEGER;
        } else if (auto phiNode = llvm::dyn_cast<llvm::PHINode>(current)) {

            std::optional<ValueType> ret = {};
            for (auto& incomingUse : phiNode->incoming_values()) {
                auto incomingVal = incomingUse.get();
                if (!llvm::is_contained(passedInstrs, incomingVal)) {
                    auto pointerStatus = is_unconfirmed_pointer(dataLayout, incomingVal);
                    if (pointerStatus.has_value()) {
                        if (ret.has_value()) {
                            if (pointerStatus == INTEGER && ret == POINTER)
                                pointerStatus = POINTER;
                            else if (pointerStatus == POINTER && ret == INTEGER)
                                ret = POINTER;
                            
                            if (pointerStatus.value() != ret.value()) {
                                llvm::outs() << "At phinode: " << *phiNode << "\n";
                                llvm::outs() << "pointerStatus is " << pointerStatus.value() << " and ret is " << ret.value() << "\n";
                            }
                            assert(pointerStatus.value() == ret.value());
                        } else ret = pointerStatus;
                    } else return {};
                } else return {};
            }
            return ret;
        } else if (auto selectInst = llvm::dyn_cast<llvm::SelectInst>(current)) {
            auto optionA = is_unconfirmed_pointer(dataLayout, selectInst->getTrueValue());
            auto optionB = is_unconfirmed_pointer(dataLayout, selectInst->getFalseValue());

            if (optionA.has_value() && optionB.has_value()) {
                if (optionA == POINTER && optionB == INTEGER)
                    optionB = POINTER;
                if (optionA == INTEGER && optionB == POINTER)
                    optionA = POINTER;

                if (optionA.value() != optionB.value()) {
                    llvm::outs() << "optionA: " << optionA.value() << "\n";
                    llvm::outs() << "optionB: " << optionB.value() << "\n";
                }
                ASSERT_ELSE_UNKOWN(optionA.value() == optionB.value(), selectInst);
                return optionA.value();
            } else return {};
        } else if (auto gepInst = llvm::dyn_cast<llvm::GetElementPtrInst>(current)) {
            current = gepInst->getPointerOperand();
        } else if (auto gepOperator = llvm::dyn_cast<llvm::GEPOperator>(current)) {
            current = gepOperator->getPointerOperand();
        } else if (llvm::isa<llvm::LoadInst, llvm::CallBase, llvm::Argument, llvm::ExtractElementInst, llvm::ExtractValueInst>(current)) {
            return {};
        } else if (llvm::isa<llvm::InsertElementInst, llvm::InsertValueInst>(current)) {
            return {}; // these are aggregates/vectors, not pointers.
            // If we want to continue tracking these, we have to represent pointers differently (as val + idx)
        } else if (auto binaryOp = llvm::dyn_cast<llvm::BinaryOperator>(current)) {
            auto lhs = is_unconfirmed_pointer(dataLayout, binaryOp->getOperand(0));
            auto rhs = is_unconfirmed_pointer(dataLayout, binaryOp->getOperand(1));

            if (!lhs.has_value() || !rhs.has_value())
                return {};

            switch (binaryOp->getOpcode()) {
                case llvm::BinaryOperator::SDiv: {
                    // Considering everything invalid except normal integer division
                    // ptr / int = INVALID
                    // ptr / ptr = INVALID
                    // ptr / neg_ptr = INVALID
                    // int / int = int
                    // int / ptr = INVALID
                    // int / neg_ptr = INVALID
                    // neg_ptr / int = INVALID
                    // neg_ptr / ptr = INVALID
                    // neg_ptr / neg_ptr = INVALID
                    if (lhs.has_value() && rhs.has_value() && lhs == INTEGER && rhs == INTEGER)
                        return INTEGER;
                    else HANDLE_UNKOWN_VALUE(binaryOp);

                } break;
                case llvm::BinaryOperator::Xor: {
                    // only case i know where this would happen is "ptr xor -1" to flip all pointer bits as a way to invert the sign (i think)
                    assert(rhs.has_value() && lhs.has_value());
                    if (!(lhs == POINTER && rhs == INTEGER))
                        HANDLE_UNKOWN_VALUE(binaryOp);
                    assert(lhs == POINTER && rhs == INTEGER);
                    ASSERT_ELSE_UNKOWN(binaryOp->getNumUses() == 1, binaryOp);
                    assert(llvm::cast<llvm::ConstantInt>(binaryOp->getOperand(1))->equalsInt(-1));
                    return NEGATED_POINTER;
                } break;
                case llvm::BinaryOperator::LShr:
                case llvm::BinaryOperator::Shl: {
                    // why would you ever shift a pointer?
                    if (lhs.has_value() && rhs.has_value() && lhs == INTEGER && rhs == INTEGER) {
                        return INTEGER;
                    } else {
                        HANDLE_UNKOWN_VALUE(binaryOp);
                    }
                } break;
                case llvm::BinaryOperator::Or: {
                    // I should treat ors like adds, rather than ands, since they only set bits
                    // ptr | int = ptr
                    // ptr | ptr = INVALID
                    // ptr | neg_ptr = INVALID
                    // int | int = int
                    // int | ptr = ptr
                    // int | neg_ptr = INVALID
                    // neg_ptr | int = INVALID
                    // neg_ptr | ptr = INVALID
                    // neg_ptr | neg_ptr = INVALID
                    if (lhs.has_value() && rhs.has_value()) {
                        assert(lhs != NEGATED_POINTER && rhs.value() != NEGATED_POINTER);

                        if ((lhs == POINTER && rhs == INTEGER) || (rhs == POINTER && lhs == INTEGER)) {
                            return POINTER;
                        } else {
                            assert(lhs == INTEGER && rhs == INTEGER);
                            return INTEGER;
                        }
                    } else HANDLE_UNKOWN_VALUE(binaryOp);
                    
                } break;
                case llvm::BinaryOperator::And: {
                    // ptr & int = ptr or int (depends on int: UINT64_MAX << 8 gives ptr, UINT64_MAX >> 48 gives int)
                    // ptr & ptr = INVALID
                    // ptr & neg_ptr = INVALID
                    // int & int = int
                    // int & ptr = ptr or int
                    // int & neg_ptr = INVALID
                    // neg_ptr & int = INVALID
                    // neg_ptr & ptr = INVALID
                    // neg_ptr & neg_ptr = INVALID
                    if (lhs.has_value() && rhs.has_value()) {
                        assert(lhs != NEGATED_POINTER && rhs.value() != NEGATED_POINTER);

                        if ((lhs == POINTER && rhs == INTEGER) || (rhs == POINTER && lhs == INTEGER)) {
                            auto mask = binaryOp->getOperand(rhs == INTEGER);
                            // TODO:: Instead of testing for constantInt, I could do some constant folding or knownbits analysis
                            // also, a common case is to have the page size and stuff, which is technically not a compile time
                            // constant, but maybe i could identify those functions etc idk
                            if (auto constantMask = llvm::dyn_cast<llvm::ConstantInt>(mask)) {
                                uint64_t maskVal = constantMask->getZExtValue();
                                std::bitset<64> bitset{maskVal};

                                if (bitset.count() >= 32) {
                                    if (std::countl_one(maskVal) >= 32)
                                        return POINTER;
                                    else if (std::__countl_zero(maskVal) >= 32)
                                        return INTEGER;
                                    else HANDLE_UNKOWN_VALUE(binaryOp);
                                } else return INTEGER;
                            } else return {}; 
                        } else {
                            assert(lhs == INTEGER && rhs == INTEGER);
                            return INTEGER;
                        }
                    } else HANDLE_UNKOWN_VALUE(binaryOp);
                } break;
                case llvm::BinaryOperator::Add: {
                    // ptr + int = ptr
                    // ptr + ptr = INVALID (2)
                    // ptr + neg_ptr = ptr - ptr = int
                    // int + int = int
                    // int + ptr = ptr
                    // int + neg_ptr = int - ptr = neg_ptr
                    // neg_ptr + int = neg_ptr
                    // neg_ptr + ptr = ptr - ptr = int
                    // neg_ptr + neg_ptr = - (ptr + ptr) = INVALID (-2)
                    if (lhs.has_value() && rhs.has_value()) {
                        int result = lhs.value() + rhs.value();
                        if (!(abs(result) <= 1)) {
                            llvm::outs() << "lhs: " << lhs.value() << ", rhs: " << rhs.value() << "\n";
                            HANDLE_UNKOWN_VALUE(binaryOp);
                        }
                        assert(abs(result) <= 1);
                        return static_cast<ValueType>(result);
                    } else HANDLE_UNKOWN_VALUE(binaryOp);
                } break;
                case llvm::BinaryOperator::Sub: {
                    // ptr - int = ptr 
                    // ptr - ptr = int
                    // ptr - neg_ptr = ptr + ptr = INVALID (2)
                    // int - int = int
                    // int - ptr = neg_ptr
                    // int - neg_ptr = ptr
                    // neg_ptr - int = neg_ptr
                    // neg_ptr - ptr = neg_ptr + neg_ptr = -(ptr + ptr) = INVALID (-2)
                    // neg_ptr - neg_ptr = neg_ptr + ptr = ptr - ptr = int

                    if (lhs.has_value() && rhs.has_value()) {
                        int result = lhs.value() - rhs.value();
                        assert(abs(result) <= 1);
                        return static_cast<ValueType>(result);
                    } else HANDLE_UNKOWN_VALUE(binaryOp);
                } break;
                case llvm::BinaryOperator::Mul: {
                    // ptr * int = ptr 
                    // ptr * ptr = INVALID
                    // ptr * neg_ptr = INVALID
                    // int * int = int
                    // int * ptr = ptr
                    // int * neg_ptr = neg_ptr
                    // neg_ptr * int = neg_ptr
                    // neg_ptr * ptr = INVALID
                    // neg_ptr * neg_ptr = INVALID

                    assert(lhs.has_value() && rhs.has_value());

                    if (lhs == POINTER || lhs == NEGATED_POINTER) {
                        ASSERT_ELSE_UNKOWN(rhs == INTEGER, binaryOp);
                        auto rh = llvm::dyn_cast<llvm::ConstantInt>(binaryOp->getOperand(1));
                        ASSERT_ELSE_UNKOWN(rh && rh->getValue().abs() == 1, binaryOp);
                        return lhs;
                    } else if (rhs == POINTER || rhs == NEGATED_POINTER) {
                        ASSERT_ELSE_UNKOWN(lhs == INTEGER, binaryOp);
                        auto lh = llvm::dyn_cast<llvm::ConstantInt>(binaryOp->getOperand(0));
                        ASSERT_ELSE_UNKOWN(lh && lh->getValue().abs() == 1, binaryOp);
                        return POINTER;
                    } else {
                        ASSERT_ELSE_UNKOWN(lhs == INTEGER && rhs == INTEGER, binaryOp);
                        return INTEGER;
                    }
                    assert(false);
                } break;
                default: {
                    HANDLE_UNKOWN_VALUE(current);
                }
            }
        } else if (auto constantExpr = llvm::dyn_cast<llvm::ConstantExpr>(current)) {
            switch (constantExpr->getOpcode()) {
                case llvm::Instruction::IntToPtr: {
                    assert(dataLayout.getTypeSizeInBits(current->getType()) == dataLayout.getTypeSizeInBits(constantExpr->getOperand(0)->getType()));
                    assert(dataLayout.getTypeSizeInBits(current->getType()) == 64);
                    current = constantExpr->getOperand(0);
                } break;
                default: {
                    llvm::outs() << "Opcode: " << constantExpr->getOpcodeName() << "\n";
                    llvm::outs() << "Is unaryOperator: " << llvm::isa<llvm::UnaryOperator>(current) << "\n";
                    HANDLE_UNKOWN_VALUE(current);
                } break;
            }
        } else HANDLE_UNKOWN_VALUE(current);

        assert(oldCurrent != current);
        assert(!llvm::isa<llvm::Argument>(oldCurrent));
        auto func = functionOf(oldCurrent);
        if (func) {
            auto oldInst = llvm::cast<llvm::Instruction>(oldCurrent);
            auto& postDomTree = FAM.getResult<llvm::PostDominatorTreeAnalysis>(*func);
            auto oldNode = postDomTree.getNode(oldInst->getParent());
            auto curNode = postDomTree.getNode(llvm::isa<llvm::Instruction>(current) ? llvm::cast<llvm::Instruction>(current)->getParent() : &func->getEntryBlock());
            if (!postDomTree.dominates(oldNode, curNode))
                return std::nullopt;
        }
    }
    assert(is_confirmed_pointer(current));
    return POINTER;
}

std::optional<PointerDetector::BinaryOpValueTypes> PointerDetector::findBinaryOpValueTypes(llvm::BinaryOperator* binaryOp) {
    auto lhs = binaryOp->getOperand(0);
    auto rhs = binaryOp->getOperand(1);

    auto& dataLayout = module.getDataLayout();

    if (llvm::isa<llvm::ConstantInt>(rhs)) {
        assert(!llvm::isa<llvm::ConstantInt>(lhs));
        return BinaryOpValueTypes{lhs, rhs};
    } else if (llvm::isa<llvm::ConstantInt>(lhs)) {
        assert(!llvm::isa<llvm::ConstantInt>(rhs));
        return BinaryOpValueTypes{rhs, lhs};
    } else if (is_confirmed_pointer(lhs)) {
        assert(!is_confirmed_pointer(rhs));
        return BinaryOpValueTypes{lhs, rhs};
    } else if(is_confirmed_pointer(rhs)) {
        assert(!is_confirmed_pointer(lhs));
        return BinaryOpValueTypes{rhs, lhs};
    } else if (auto lhStatus = is_unconfirmed_pointer(dataLayout, lhs)) {
        assert(lhStatus.has_value());
        auto rhStatus = is_unconfirmed_pointer(dataLayout, rhs);
        if (lhStatus == PointerDetector::INTEGER) {
            assert(!rhStatus.has_value() || rhStatus.value() == PointerDetector::POINTER);
            return BinaryOpValueTypes{rhs, lhs};
        } else if (lhStatus == PointerDetector::POINTER) {
            assert(!rhStatus.has_value() || rhStatus.value() == PointerDetector::INTEGER);
            return BinaryOpValueTypes{lhs, rhs};
        } else HANDLE_UNKOWN_VALUE(binaryOp);
    } else if (auto rhStatus = is_unconfirmed_pointer(dataLayout, rhs)) {
        assert(rhStatus.has_value());
        auto lhStatus = is_unconfirmed_pointer(dataLayout, rhs);
        if (rhStatus == PointerDetector::INTEGER && (!lhStatus.has_value() || lhStatus.value() == PointerDetector::POINTER)) {
            return BinaryOpValueTypes{rhs, lhs};
        } else if (rhStatus == PointerDetector::POINTER && (!lhStatus.has_value() || lhStatus.value() == PointerDetector::INTEGER)) {
            return BinaryOpValueTypes{lhs, rhs};
        } else HANDLE_UNKOWN_VALUE(binaryOp);
    } else return std::nullopt;
}

llvm::Function* PointerDetector::functionOf(llvm::Value* val) {
    if (auto inst = llvm::dyn_cast<llvm::Instruction>(val))
        return inst->getFunction();
    else if (auto arg = llvm::dyn_cast<llvm::Argument>(val))
        return arg->getParent();
    else 
        return nullptr;
}

PointerDetectionAnalysis::Result PointerDetectionAnalysis::run(llvm::Module &M, [[maybe_unused]] llvm::ModuleAnalysisManager &MAM) {
    return PointerDetector(M, MAM);
}