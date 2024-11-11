#include <llvm-utils/addressability/addressability.h>

void collectIntraProceduralPtrEscapes(llvm::Value* ptr, llvm::DenseSet<llvm::Use*> ptrEscapes, const PointerDetector& pointerInfo) {
    static thread_local std::vector<llvm::Value*> passedInstrs;
    const auto size = passedInstrs.size();
    run_on_destruct resetPassedInstrs([&](){
        assert(passedInstrs.size() >= 1);
        assert(size <= passedInstrs.size());
        passedInstrs.erase(passedInstrs.begin() + size, passedInstrs.end());
        assert(passedInstrs.size() == size);
    });

    passedInstrs.push_back(ptr);

    for (auto& ptrUse : ptr->uses()) {
        auto user = ptrUse.getUser();
        
        if (auto call = llvm::dyn_cast<llvm::CallBase>(user)) {
            if (call->getCalledOperandUse() != ptrUse)
                ptrEscapes.insert(&ptrUse);
        } else if (auto store = llvm::dyn_cast<llvm::StoreInst>(user)) {
            if (store->getPointerOperandIndex() != ptrUse.getOperandNo()) {
                ASSERT_ELSE_UNKOWN(ptr == store->getValueOperand(), store);
                ptrEscapes.insert(&ptrUse);
            }
        } else if (auto ret = llvm::dyn_cast<llvm::ReturnInst>(user)) {
            ptrEscapes.insert(&ptrUse);
        } else if (llvm::isa<llvm::InsertValueInst, llvm::InsertElementInst>(user)) {
            // wouldnt know how the pointer ends up in any of the other args
            ASSERT_ELSE_UNKOWN(ptrUse == user->getOperandUse(1), user);
            // we _could_ continue here, but especially if the idx is non-constant we wont find much
            ptrEscapes.insert(&ptrUse);
        } else if (auto agg = llvm::dyn_cast<llvm::ConstantAggregate>(user)) {
            // we _could_ continue here, but who knows what happens to the value this is initializing
            ptrEscapes.insert(&ptrUse);
        } else if (auto global = llvm::dyn_cast<llvm::GlobalVariable>(user)) {
            // initializer for a global
            //  we can continue looking if this global is constant & internal
            //  or if is not constant but "like" a constant, (and not publically linked)
            //  we'd have to consider its aliases as well, and look through casts etc
            // for now, let's just assume this is opaque, since we would still have to wrap here if any of
            //  the previous conditions are not perfectly met
            ptrEscapes.insert(&ptrUse);
        } else if (auto binaryOp = llvm::dyn_cast<llvm::BinaryOperator>(user)) {
            auto pointerStatus = pointerInfo.handle_unconfirmed_binaryOp(binaryOp);
            using enum PointerDetector::ValueType;
            if (!pointerStatus.has_value() || *pointerStatus == NEGATED_POINTER)
                ptrEscapes.insert(&ptrUse); // some opaque thing we don't understand
            else if (*pointerStatus == POINTER)
                collectIntraProceduralPtrEscapes(binaryOp, ptrEscapes, pointerInfo);
            // else INTEGER -> this is an offset, don't have to arithcheck it here
        } else if (auto icmp = llvm::dyn_cast<llvm::ICmpInst>(user)) {
            // ignore -> if these comparisons are with OOB pointers, it's likely the end iterator
            //  those will not be considered confirmed pointers since they are not dereferences
            //  so we shouldn't wrap the comparison operator either
            // about propagation/information leakage: the other operand will have to have been "based on"
            //  the one we're looking for -> we'll already be looking for it through a previous gep or w/e
            //  besides, like always, we can't really explore one of these operands "under the condition that"
            //  this icmp returns a particular value. so it'd quickly become an over-estimation
        } else if (auto phi = llvm::dyn_cast<llvm::PHINode>(user)) {
            ASSERT_ELSE_UNKOWN(!llvm::isa<llvm::BasicBlock>(ptr), phi);
            if (!llvm::is_contained(passedInstrs, ptr))
                collectIntraProceduralPtrEscapes(phi, ptrEscapes, pointerInfo);
            // else we've already seen it, no more escapes to collect
        } else if (llvm::isa<llvm::SelectInst, llvm::FreezeInst>(user)) {
            collectIntraProceduralPtrEscapes(user, ptrEscapes, pointerInfo);
        } else if (auto cast = llvm::dyn_cast<llvm::CastInst>(user)) {
            if (cast->getDestTy()->isPointerTy() || cast->getDestTy()->isIntegerTy(64))
                collectIntraProceduralPtrEscapes(cast, ptrEscapes, pointerInfo);
        } else if (auto bitcastOp = llvm::dyn_cast<llvm::BitCastOperator>(user)) {
            if (bitcastOp->getDestTy()->isPointerTy() || bitcastOp->getDestTy()->isIntegerTy(64))
                collectIntraProceduralPtrEscapes(bitcastOp, ptrEscapes, pointerInfo);
        } else if (auto gep = llvm::dyn_cast<llvm::GEPOperator>(user)) {
            if (gep->getOperandUse(gep->getPointerOperandIndex())) {
                if (gep->getType()->isPointerTy())
                    collectIntraProceduralPtrEscapes(gep, ptrEscapes, pointerInfo);
                else // SPEC06 mcf triggers this: a gep with vector indices gives a vector of pointers
                    ptrEscapes.insert(&ptrUse);
            } else {
                // ive never seen this outside of nginx, never with more than 1 idx
                ASSERT_ELSE_UNKOWN(gep->getNumIndices() == 1, gep);
                // somehow another pointer being used as the index in the gep?
                //  is the pointeroperand an index or something?
                auto pointerOperandStatus = pointerInfo.is_unconfirmed_pointer(gep->getPointerOperand());
                using enum PointerDetector::ValueType;
                if (pointerOperandStatus.has_value()) {
                    if (*pointerOperandStatus == POINTER)
                        HANDLE_UNKOWN_VALUE(gep); // ptr + ptr ???
                    else if (*pointerOperandStatus == INTEGER)
                        // follow the user here! inverted gep
                        collectIntraProceduralPtrEscapes(gep, ptrEscapes, pointerInfo);
                    else
                        ASSERT_ELSE_UNKOWN(*pointerOperandStatus == NEGATED_POINTER, gep);
                } else {
                    // totally unclear going into the gep here. might create a relative pointer
                    // this is an escape site
                    ptrEscapes.insert(&ptrUse);
                }
            }            
        } else if (llvm::isa<llvm::LoadInst>(user)) {
            // ignore
        } else if (auto atomicRMW = llvm::dyn_cast<llvm::AtomicRMWInst>(user)) {
            ASSERT_ELSE_UNKOWN(atomicRMW->getOperandUse(atomicRMW->getPointerOperandIndex()) == ptrUse, user);
            // just like a load, ignore
        } else if (auto cmpxchg = llvm::dyn_cast<llvm::AtomicCmpXchgInst>(user)) {
            if (cmpxchg->getOperandUse(cmpxchg->getPointerOperandIndex()) == ptrUse) {
                // just like a load, ignore
            } else if (cmpxchg->getOperandUse(2) == ptrUse) { // operand(2) == newvaloperand
                // this is a store
                ptrEscapes.insert(&ptrUse);
            } else { // a pointer as the comparison value?? treat like icmp
                ASSERT_ELSE_UNKOWN(cmpxchg->getOperandUse(1) == ptrUse, cmpxchg);
                // ignore like icmp
            }
        } else if (auto switchInst = llvm::dyn_cast<llvm::SwitchInst>(user)) {
            // operand 0 is the condition
            ASSERT_ELSE_UNKOWN(switchInst->getOperandUse(0) == ptrUse, user);
            // ignore. i refuse to buy into perlbench's bullshit that compile-time constant labels could somehow be valid pointer values
        } else if (auto landingPad = llvm::dyn_cast<llvm::LandingPadInst>(user)) {
            ASSERT_ELSE_UNKOWN(llvm::isa<llvm::Constant>(ptrUse.get()), ptrUse.get());
            // the value doesnt propagate anywhere. ignore
        } else if (auto constExpr = llvm::dyn_cast<llvm::ConstantExpr>(user)) {
            // too much to handle. Handle it like an instruction
            auto inst = constExpr->getAsInstruction();
            // this is very fucking weird but it works
            constExpr->replaceAllUsesWith(inst);
            collectIntraProceduralPtrEscapes(inst, ptrEscapes, pointerInfo);
            inst->replaceAllUsesWith(constExpr);
            inst->deleteValue();
        } else HANDLE_UNKOWN_VALUE(user);
    }
}
