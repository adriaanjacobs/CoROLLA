#include <llvm-utils/addressability/addressability.h>

#include <llvm-utils/callsiteanalysis/callsiteanalysis.h>
#include <llvm-utils/safetyanalysis/safetyanalysis.h>

// interprocedural def-use walk to see what instructions this allocSites flows to
//  mostly used to prune out safe stack allocations
//  "safe"/"unsafe" is kind of an over-statement here
//  more like "may be used as pointer operand in the unsafeaccesses"
bool ptrMayReachUnsafeAccesses(llvm::Value* ptr, const UnsafeAccessInfo& unsafeAccessInfo, const CallSiteAnalysisResult& callSiteAnalysis) {
    static thread_local std::vector<llvm::Value*> passedInstrs;
    const auto size = passedInstrs.size();
    run_on_destruct resetPassedInstrs([&](){
        assert(passedInstrs.size() >= 1);
        assert(size <= passedInstrs.size());
        passedInstrs.erase(passedInstrs.begin() + size, passedInstrs.end());
        assert(passedInstrs.size() == size);
    });

    if (llvm::is_contained(passedInstrs, ptr))
        return false;

    passedInstrs.push_back(ptr);
    
    auto& unsafeAccesses = unsafeAccessInfo.unsafeAccesses;
    for (auto& use : ptr->uses()) {
        auto const user = use.getUser();
        bool isUnsafeUse = [&] () {
            if (auto store = llvm::dyn_cast<llvm::StoreInst>(user)) {
                if (store->getValueOperand() == ptr)
                    return true;
                return unsafeAccesses.contains(store);
            } else if (auto rmw = llvm::dyn_cast<llvm::AtomicRMWInst>(user)) {
                if (ptr == rmw->getValOperand())
                    return false;
                return unsafeAccesses.contains(rmw); // same as cmpxchg
            } else if (auto cmpxchg = llvm::dyn_cast<llvm::AtomicCmpXchgInst>(user)) {
                if (ptr == cmpxchg->getCompareOperand() || ptr == cmpxchg->getNewValOperand())
                    return false;
                return unsafeAccesses.contains(cmpxchg); // will always be false now, but maybe we should include these at some point
            } else if (llvm::isa<llvm::InsertElementInst, llvm::InsertValueInst, llvm::ConstantAggregate, llvm::GlobalVariable>(user)) {
                // my primary goal is to reduce instrumentation on unreachable alloca's. globals are basically free
                return true; // not tracking that shit down just yet
            } else if (auto load = llvm::dyn_cast<llvm::LoadInst>(user)) {
                return unsafeAccesses.contains(load);
            } else if (auto call = llvm::dyn_cast<llvm::CallBase>(user)) {
                auto calledFunc = call->getCalledFunction();
                if (!calledFunc)
                    return true;
                ASSERT_ELSE_UNKOWN(call->getCalledOperand() != ptr, call);
                // the onlyreadsmemory also implies nocapture (?)
                if (unsafeAccessInfo.onlyStores && calledFunc->onlyReadsMemory())
                    return false;
                auto calledArgIdx = call->getArgOperandNo(&use);
                if (calledArgIdx >= calledFunc->arg_size())
                    return true;
                auto formalArg = calledFunc->getArg(calledArgIdx);
                // readonly implies nocapture (?)
                if (unsafeAccessInfo.onlyStores && formalArg->hasAttribute(llvm::Attribute::ReadOnly))
                    return false;
                if (calledFunc->isDeclaration()) // FIXME:: i should probably specify memcpy/memcmp/memmove here                
                    return true;
                return ptrMayReachUnsafeAccesses(calledFunc->getArg(calledArgIdx), unsafeAccessInfo, callSiteAnalysis);
            } else if (auto ret = llvm::dyn_cast<llvm::ReturnInst>(user)) {
                const auto& callSiteInfo = callSiteAnalysis.getCallSiteInfo(ret->getFunction());
                if (!callSiteInfo.isOnlyDirectlyCalled())
                    return true;
                for (auto callSite : callSiteInfo.directCallSites)
                    if (ptrMayReachUnsafeAccesses(callSite, unsafeAccessInfo, callSiteAnalysis))
                        return true;
                return false;
            } else if (llvm::isa<llvm::PHINode, llvm::SelectInst, llvm::BitCastOperator, llvm::PtrToIntOperator>(user)) {
                return ptrMayReachUnsafeAccesses(user, unsafeAccessInfo, callSiteAnalysis);
            } else if (auto cast = llvm::dyn_cast<llvm::CastInst>(user)) {
                switch (cast->getOpcode()) {
                    case llvm::Instruction::IntToPtr:
                    case llvm::Instruction::Trunc:
                    case llvm::Instruction::SExt:
                    case llvm::Instruction::ZExt:
                        if (cast->getModule()->getDataLayout().getTypeSizeInBits(cast->getType()) <= 32)
                            return false; // may miss things if stuff gets shifted around and re-added I think?
                        return ptrMayReachUnsafeAccesses(cast, unsafeAccessInfo, callSiteAnalysis);
                    default:
                        HANDLE_UNKOWN_VALUE(cast);
                }
            } else if (auto icmp = llvm::dyn_cast<llvm::ICmpInst>(user)) {
                auto notTheUser = icmp->getOperand(!use.getOperandNo());
                assert(notTheUser != user);
                return !llvm::isa<llvm::ConstantData>(notTheUser); // catches trivial comparisons against MAP_FAILED or NULL
            } else if (llvm::isa<llvm::GEPOperator, llvm::BinaryOperator>(user)) {
                return ptrMayReachUnsafeAccesses(user, unsafeAccessInfo, callSiteAnalysis); // any offset doesn't matter, later load/stores will query the safety status
            } else HANDLE_UNKOWN_VALUE(user);
        } ();

        if (isUnsafeUse)
            return true;
    }

    return false;
}


