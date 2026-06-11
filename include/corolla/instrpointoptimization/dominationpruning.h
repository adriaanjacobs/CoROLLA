#pragma once

#include "instrumentationpoint.h"

#include <llvm/IR/Dominators.h>
#include <llvm/Analysis/LoopInfo.h>

bool pruneDominatedChecks(
    llvm::DenseMap<InstrumentationPoint*, llvm::DenseSet<llvm::Use*>>& pointToUses, 
    std::function<llvm::Value*(llvm::Value*)> stripPointerCasts,
    llvm::DominatorTree& DT,
    llvm::LoopInfo& LI
);

void pruneDominatedAccesses(
    llvm::FunctionAnalysisManager& FAM, 
    llvm::DenseSet<llvm::Instruction*>& loadAndStores, 
    std::function<llvm::Value*(llvm::Value*)> stripPointerCasts
);

