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

    InstrumentationPoint(llvm::Instruction* insertBefore, llvm::Value* pointerOperand) : 
        insertBefore{insertBefore}, pointerOperand{pointerOperand}
    {}

    InstrumentationPoint(llvm::Instruction* insertBefore, llvm::Value* pointerOperand, llvm::Value* endOfAddressRange) : 
        insertBefore{insertBefore}, pointerOperand{pointerOperand}, endOfAddressRange{endOfAddressRange}
    {}

    bool isRangeCheck() const {
        return pointerOperand != endOfAddressRange;
    }

    bool operator==(const InstrumentationPoint& other) const {
        return std::memcmp(this, &other, sizeof(*this));
    }

} __attribute__((packed)); // to make sure the memcmp works wrt padding

class LoopHoister {
    llvm::Module& module;
    llvm::ModuleAnalysisManager& MAM;

    // map because DenseMap moves on try_emplace and SCEVExpander can't handle that
    std::map<llvm::Function*, llvm::SCEVExpander> scevExpanders;
    llvm::SCEVExpander& getOrCreateSCEVExpander(llvm::Function* func, llvm::ScalarEvolution& SCEV);

    llvm::Value* tryExpandSCEV(const llvm::SCEV* scev, llvm::Type* expandedTy, llvm::Instruction* insertBefore);

public:
    LoopHoister(llvm::Module& M, llvm::ModuleAnalysisManager& MAM);

    // Maximally hoist logs in loops into preheaders
    void hoistLoopBoundMemAccesses(llvm::DenseMap<llvm::Function*, llvm::DenseMap<llvm::Use*, llvm::DenseSet<InstrumentationPoint*>>>& funcToInstPoints);
};



