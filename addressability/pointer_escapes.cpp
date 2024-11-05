#include <llvm-utils/addressability/addressability.h>

void collectIntraProceduralPtrEscapes(llvm::Value* ptr, llvm::DenseSet<llvm::Use*> ptrEscapes) {
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
        } else if (llvm::isa<llvm::InsertValueInst, llvm::InsertElementInst>(user)) {
            // wouldnt know how the pointer ends up in any of the other args
            ASSERT_ELSE_UNKOWN(ptrUse == user->getOperandUse(1), user);
            // we _could_ continue here, but especially if the idx is non-constant we wont find much
            ptrEscapes.insert(&ptrUse);
        } else if (llvm::isa<llvm::LoadInst>(user)) {
            // ignore
        } else HANDLE_UNKOWN_VALUE(user);
    }
}
