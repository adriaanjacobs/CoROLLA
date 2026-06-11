#include <corolla/safetyanalysis/safetyanalysis.h>

#include <corolla/util.h>
#include <corolla/instrpointoptimization/dominationpruning.h>

llvm::AnalysisKey OSOVAnalysis::Key;

OSOVAnalysis::Result::Result(llvm::Function& F, llvm::FunctionAnalysisManager& FAM) : 
    F{F}, FAM{FAM}, DL{F.getParent()->getDataLayout()},
    OSOV {
        DL,
        &FAM.getResult<llvm::TargetLibraryAnalysis>(F),
        F.getContext(),
        llvm::ObjectSizeOpts{
            .EvalMode = llvm::ObjectSizeOpts::Mode::Min,
            .RoundToAlign = true,
            .NullIsUnknownSize = false,
        }
    }
{

    llvm::DenseSet<llvm::Instruction*> unsafeInsts;
    for (auto& bb : F) 
        for (auto& inst : bb) 
            if (auto ptrUse = getLoadStorePointerOperandUse(&inst)) 
                if (!computeIsInBounds(ptrUse)) 
                    unsafeInsts.insert(&inst);

    pruneDominatedAccesses(FAM, unsafeInsts, [&] (llvm::Value* ptr) {
        auto retval = ptr->stripPointerCastsForAliasAnalysis();
        assert(retval);
        return retval;
    });

    for (auto inst : unsafeInsts)
        unsafeUses.insert(getLoadStorePointerOperandUse(inst));
    assert(!unsafeUses.contains(nullptr));
}

bool OSOVAnalysis::Result::computeIsInBounds(llvm::Use* PtrUse) {
    auto SizeOffset = OSOV.compute(PtrUse->get());
    if (OSOV.bothKnown(SizeOffset)) {
        llvm::APInt Size = SizeOffset.first;
        llvm::APInt Offset = SizeOffset.second;
        uint64_t AccessSize = DL.getTypeStoreSize(llvm::getLoadStoreType(llvm::cast<llvm::Instruction>(PtrUse->getUser())));
        
        if (Offset.sge(0)) {
            bool Overflow = false;
            llvm::APInt EndOffset = Offset.uadd_ov(llvm::APInt(Offset.getBitWidth(), AccessSize), Overflow);
            if (!Overflow && EndOffset.ule(Size)) {
                return true; // Statically safe
            }
        }
    }

    return false;
}

bool OSOVAnalysis::Result::isInBounds(llvm::Use* PtrUse) {
    return !unsafeUses.contains(PtrUse);
}

OSOVAnalysis::Result OSOVAnalysis::run(llvm::Function& F, [[maybe_unused]] llvm::FunctionAnalysisManager& FAM) {
    return Result{F, FAM};
}
