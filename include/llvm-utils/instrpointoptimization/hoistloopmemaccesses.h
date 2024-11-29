#pragma once

#include <llvm/IR/PassManager.h>
#include <llvm/IR/Module.h>
#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Transforms/Utils/ScalarEvolutionExpander.h>

#include <map>

struct InstrumentationPoint {
    llvm::Instruction* insertBefore;
    llvm::Value* pointerOperand;
    llvm::Value* endOfAddressRange = pointerOperand;
    bool unsoundlyHoisted = false;

    InstrumentationPoint(llvm::Instruction* insertBefore, llvm::Value* pointerOperand) : 
        insertBefore{insertBefore}, pointerOperand{pointerOperand}
    {}

    bool isRangeCheck() const {
        return pointerOperand != endOfAddressRange;
    }

    void print() {
        llvm::errs() << "ptr: " << *pointerOperand << "\n";
        if (endOfAddressRange != pointerOperand)
            llvm::errs() << "end: " << *endOfAddressRange << "\n";
        llvm::errs() << "insertbefore: " << *insertBefore << "\n";
    }
};

class LoopHoister {
    llvm::Module& module;
    llvm::ModuleAnalysisManager& MAM;

    // map because DenseMap moves on try_emplace and SCEVExpander can't handle that
    std::map<llvm::Function*, llvm::SCEVExpander> scevExpanders;
    llvm::SCEVExpander& getOrCreateSCEVExpander(llvm::Function* func, llvm::ScalarEvolution& SCEV);

    llvm::Value* tryExpandSCEV(const llvm::SCEV* scev, llvm::Type* expandedTy, llvm::Instruction* insertBefore);

    llvm::Use* findLoopInvariantPointerBaseUse(llvm::Loop* loop, llvm::Value* pointerOperand);
    llvm::Value* computeICMP(llvm::ICmpInst::Predicate pred, llvm::Value* lhs, llvm::Value* rhs, llvm::Instruction* insertBefore);

public:
    LoopHoister(llvm::Module& M, llvm::ModuleAnalysisManager& MAM);

    // Maximally hoist logs in loops into preheaders
    void hoistLoopBoundMemAccesses(llvm::DenseMap<llvm::Function*, llvm::DenseMap<llvm::Use*, InstrumentationPoint*>>& funcToInstPoints, bool permitNonMustExecute = false);
};



