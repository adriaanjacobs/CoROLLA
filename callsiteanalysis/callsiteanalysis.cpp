#include <llvm-utils/callsiteanalysis/callsiteanalysis.h>

#include <llvm-utils/util.h>

llvm::AnalysisKey CallSiteAnalysis::Key;

CallSiteAnalysisResult::CallSiteAnalysisResult(llvm::Module& module, llvm::ModuleAnalysisManager& MAM) :
    module{module}, MAM{MAM}
{}

const CallSiteAnalysisResult::CallSiteInfo& CallSiteAnalysisResult::getCallSiteInfo(llvm::Function* function) const {
    auto [callSiteInfoIt, inserted] = cachedCallSiteInfo.try_emplace(function, function);
    auto& info = callSiteInfoIt->getSecond();
    if (inserted) 
        collectCallSiteInfo(function, info.directCallSites, info.opaqueUses);
    return info;
}

void CallSiteAnalysisResult::forgetCallSiteInfo(llvm::Function* function) {
    cachedCallSiteInfo.erase(function);
}

bool CallSiteAnalysisResult::CallSiteInfo::isOnlyDirectlyCalled() const {
    if (noUsesFound()) {
        ASSERT_ELSE_UNKOWN(func->getNumUses() == 0, func);
        ASSERT_ELSE_UNKOWN(!func->hasLocalLinkage(), func); // otherwise must be dead
    }
    return opaqueUses.empty();
}

bool CallSiteAnalysisResult::CallSiteInfo::noUsesFound() const {
    return directCallSites.empty() && opaqueUses.empty();
}

// whatever this returns, callSites contains all known callsites, and opaqueUses contains all uses we couldn't further analyze
// TODO(Adriaan): consider using `llvm::Function::hasAddressTaken()`
void CallSiteAnalysisResult::collectCallSiteInfo(llvm::Value* function, llvm::DenseSet<llvm::CallBase*>& callSites, llvm::DenseSet<llvm::Use*>& opaqueUses) const {
    auto& dataLayout = module.getDataLayout();
    if (function->getNumUses() == 0) 
        return;

    for (auto& funcUse : function->uses()) {
        auto user = funcUse.getUser();
        assert(function == funcUse.get());
        if (auto call = llvm::dyn_cast<llvm::CallBase>(user)) {
            if (call->getCalledFunction() != function) // the function is passed as argument
                opaqueUses.insert(&funcUse);
            else 
                callSites.insert(call);
        } else if (auto storeInst = llvm::dyn_cast<llvm::StoreInst>(user)) {
            ASSERT_ELSE_UNKOWN(storeInst->getValueOperand() == function, user);
            opaqueUses.insert(&funcUse);
        } else if (llvm::isa<llvm::ConstantAggregate, llvm::GlobalVariable, llvm::PtrToIntOperator>(user)) {
            opaqueUses.insert(&funcUse);
        } else if (auto phiNode = llvm::dyn_cast<llvm::PHINode>(user)) {
            opaqueUses.insert(&funcUse);
        } else if (auto select = llvm::dyn_cast<llvm::SelectInst>(user)) {
            ASSERT_ELSE_UNKOWN(select->getCondition() != function, user);
            opaqueUses.insert(&funcUse);
        } else if (llvm::isa<llvm::BitCastOperator, llvm::GlobalAlias>(user)) {
            if (user->getNumUses() > 0)
                collectCallSiteInfo(user, callSites, opaqueUses);
            else
                opaqueUses.insert(&funcUse);
        } else if (auto icmp = llvm::dyn_cast<llvm::ICmpInst>(user)) {
            // the consideration here is that a icmp indicates that the program expects
            // that some function pointer _may_ refer to function here
            // Hence, the question becomes how the programmer obtained this function pointer to function?
            // It may theoretically be a wild guess based on an integer, although that is unlikely
            // There's no real way to guarantee anything here, let's just be conservative
            opaqueUses.insert(&funcUse);
        } else HANDLE_UNKOWN_VALUE(user);
    }
}

bool CallSiteAnalysisResult::getIncomingValuesForArgument(llvm::Argument* argument, llvm::DenseSet<llvm::Value*>& incomingVals) const {
    auto function = argument->getParent();

    const auto& callSiteInfo = getCallSiteInfo(function);

    bool isComplete = callSiteInfo.isOnlyDirectlyCalled() && !callSiteInfo.noUsesFound();
    // collect incoming values for the argument value, in suitable callsites
    for (auto callInst : callSiteInfo.directCallSites) {
        assert(callInst->getCalledFunction());
        if (callInst->getCalledFunction() == function && argument->getArgNo() < callInst->arg_size()) {
            auto incomingVal = callInst->getArgOperand(argument->getArgNo());
            incomingVals.insert(incomingVal);
        } else isComplete = false;
    }

    if (isComplete)
        ASSERT_ELSE_UNKOWN(!incomingVals.empty(), function);

    return isComplete;
}

CallSiteAnalysis::Result CallSiteAnalysis::run(llvm::Module &M, [[maybe_unused]] llvm::ModuleAnalysisManager &MAM) {
    return CallSiteAnalysisResult(M, MAM);
}
