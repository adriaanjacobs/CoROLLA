#include <llvm-util/pointerdetection/pointerdetection.h>
#include <llvm/IR/PassManager.h>

llvm::AnalysisKey SillyPerlAnalysis::Key;

SillyPerlAnalysis::Result SillyPerlAnalysis::run(llvm::Module& module, llvm::ModuleAnalysisManager &MAM) {
    // special for you, perlbench
    llvm::DenseSet<llvm::Instruction*> sillyPerls;
    for (auto& func : module) {
        for (auto& bb : func) {
            for (auto& inst : bb) {
                if (auto operand = llvm::getLoadStorePointerOperand(&inst)) {
                    if (auto inttoptr = llvm::dyn_cast<llvm::Operator>(operand); inttoptr && inttoptr->getOpcode() == llvm::Instruction::IntToPtr) {
                        if (llvm::isa<llvm::ConstantInt>(inttoptr->getOperand(0))) {
                            sillyPerls.insert(&inst);
                        }
                    }
                }
            }
        }
    }

#if 0
    llvm::Instruction* lowest = nullptr;
    size_t lowestSize = UINT64_MAX;
    for (auto inst : sillyPerls) {
        size_t numblocks = inst->getFunction()->size();
        if (numblocks < lowestSize) {
            lowestSize = numblocks;
            lowest = inst;
        }
    }

    if (lowest) {
        llvm::outs() << *lowest << "\n";
        llvm::outs() << "In func: '" << lowest->getFunction()->getName() << "'\n";
        assert(!"WTF perl");
    }
    // assert(lowest);
#endif
    return sillyPerls;
}