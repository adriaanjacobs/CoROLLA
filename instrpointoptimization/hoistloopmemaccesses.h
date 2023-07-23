#pragma once

#include <llvm/IR/PassManager.h>
#include <llvm/IR/Module.h>
#include <llvm/Analysis/ScalarEvolution.h>

struct InstrumentationPoint {
    llvm::Instruction* insertBefore;
    llvm::Value* pointerOperand;

    InstrumentationPoint(llvm::Instruction* insertBefore, llvm::Value* pointerOperand) : 
        insertBefore{insertBefore}, pointerOperand{pointerOperand}
    {}
};


// Maximally hoist logs in loops into preheaders
void hoistLoopBoundMemAccesses(llvm::Module&, llvm::ModuleAnalysisManager&, llvm::DenseMap<llvm::Function*, llvm::DenseMap<llvm::Instruction*, llvm::DenseSet<InstrumentationPoint*>>>& funcToInstPoints);
llvm::Value* tryExpandSCEV(llvm::Module&, llvm::ModuleAnalysisManager&, const llvm::SCEV* scev, llvm::Type* expandedTy, llvm::Instruction* insertBefore);

