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

template<typename IR>
class LoopHoister {
    // template deduction guide
    LoopHoister(IR& IRObject, llvm::AnalysisManager<IR>& IRAM);
};

struct PointerDetector;

template<>
class LoopHoister<llvm::Function> {
    llvm::Function& function;
    llvm::FunctionAnalysisManager& FAM;
    llvm::ScalarEvolution& SCEV;
    llvm::SCEVExpander SCEVExpander;
    const PointerDetector& pointerDetector;

    llvm::Value* tryExpandSCEV(const llvm::SCEV* scev, llvm::Type* expandedTy, llvm::Instruction* insertBefore);

    llvm::Use* findLoopInvariantPointerBaseUse(llvm::Loop* loop, llvm::Value* pointerOperand);
    llvm::Value* computeICMP(llvm::ICmpInst::Predicate pred, llvm::Value* lhs, llvm::Value* rhs, llvm::Instruction* insertBefore);

public:
    LoopHoister(llvm::Function& F, llvm::FunctionAnalysisManager& FAM, const PointerDetector& pointerDetector);

    enum StatCounter {
        // all
        pointsInLoops,
        // LI
        hoistedLIPoints,
        unsoundlyHoistedPoints,
        noMustExecuteLoopInvariant,
        // loop-inductive
        cantComputeBackEdgeCount,
        exitValueComputed,
        unexpandableExitvalue,
        operandDependsOnIV,
        // non-inductive
        operandDoesNotDependOnIV,
        NUM_STATS,
    };

    struct Stats : std::array<size_t, NUM_STATS> {
        Stats& operator+=(const Stats& other) {
            for (uint i = 0; i < size(); i++)
                (*this)[i] += other[i];
            return *this;
        }
    };

    // Maximally hoist logs in loops into preheaders
    Stats hoistLoopBoundMemAccesses(llvm::DenseMap<llvm::Use*, InstrumentationPoint*>& instPoints, bool permitNonMustExecute = false);
};

// legacy specialization for backward compat with LTO invocation
template<>
class LoopHoister<llvm::Module> {
    llvm::Module& module;
    llvm::ModuleAnalysisManager& MAM;
    // map because DenseMap moves on try_emplace and SCEVExpander can't handle that
    std::map<llvm::Function*, LoopHoister<llvm::Function>> funcHoisters;
    
public:
    LoopHoister(llvm::Module& M, llvm::ModuleAnalysisManager& MAM);

    // Maximally hoist logs in loops into preheaders
    void hoistLoopBoundMemAccesses(llvm::DenseMap<llvm::Function*, llvm::DenseMap<llvm::Use*, InstrumentationPoint*>>& funcToInstPoints, bool permitNonMustExecute = false);
};



