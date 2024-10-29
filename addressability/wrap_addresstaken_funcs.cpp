#include <llvm-utils/addressability/addressability.h>

llvm::Function* internalizeAndWrap(llvm::Function* func, const llvm::DenseSet<llvm::Use*>& usesToUpdate, llvm::StringRef suffix = "_internalized") {
    // drop the linkage on the original func & change its name
    // we have to do this before assigning the name to the other function
    auto ogFuncLinkage = func->getLinkage();
    func->setLinkage(llvm::GlobalValue::PrivateLinkage);
    auto ogFuncName = func->getName().str();
    func->setName(func->getName() + suffix);

    auto module = func->getParent();
    auto wrapper = llvm::Function::Create(func->getFunctionType(), ogFuncLinkage, func->getAddressSpace(), ogFuncName, module);
    wrapper->setAttributes(func->getAttributes());
    wrapper->setCallingConv(func->getCallingConv());
    for (uint i = 0; i < func->arg_size(); i++) // copy the argument names over
        wrapper->getArg(i)->setName(func->getArg(i)->getName());

    // now we create an alternative function body in the original func that calls the newFunc
    assert(wrapper->isDeclaration());
    auto entry = llvm::BasicBlock::Create(module->getContext(), "entry", wrapper);
    llvm::SmallVector<llvm::Value*> args;
    for (auto& arg : wrapper->args())
        args.push_back(&arg);

    // call the function and return its value
    auto callDirectVersion = llvm::CallInst::Create(func, args, "", entry);
    auto ret = llvm::ReturnInst::Create(entry->getContext(), callDirectVersion->getType()->isVoidTy() ? nullptr : callDirectVersion, entry);

    // update the opaque uses to use the impostor
    func->replaceUsesWithIf(wrapper, [&usesToUpdate = usesToUpdate] (llvm::Use& use) -> bool {
        return usesToUpdate.contains(&use);
    });
    
    return wrapper;
}

llvm::DenseMap<llvm::Function*, llvm::Function*> wrapAddressTakenFuncs(llvm::Module& module, llvm::ModuleAnalysisManager& MAM) {
    llvm::DenseMap<llvm::Function*, llvm::Function*> wrapperToFunc;
    auto& callSiteAnalysis = MAM.getResult<CallSiteAnalysis>(module);
    llvm::DenseMap<llvm::Function*, llvm::DenseSet<llvm::Use*>> funcsToWrap;
    for (auto& func : module) {
        if (func.isDeclaration())
            continue;
        const auto& callSiteInfo = callSiteAnalysis.getCallSiteInfo(&func);
        if (!callSiteInfo.isOnlyDirectlyCalled()) {
            // we have to emit an internal version of this function, and create a wrapper with prologue and epilogue 
            funcsToWrap[&func].insert(callSiteInfo.opaqueUses.begin(), callSiteInfo.opaqueUses.end());
        }
    }

    for (auto& [func, opaqueUses] : funcsToWrap) {
        auto wrapper = internalizeAndWrap(func, opaqueUses);
        callSiteAnalysis.forgetCallSiteInfo(func);
        wrapperToFunc[wrapper] = func;
    }

    // now invalidate all analyses
    MAM.invalidate(module, llvm::PreservedAnalyses::none());

    return wrapperToFunc;
}

    


