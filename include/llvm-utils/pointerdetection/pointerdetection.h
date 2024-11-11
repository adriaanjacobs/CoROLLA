#pragma once

#include "llvm/IR/Instructions.h"
#include <llvm/Pass.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Operator.h>
#include <llvm/Support/Casting.h>
#include <optional>
#include <llvm/Analysis/LazyBlockFrequencyInfo.h>
#include <llvm/Analysis/BasicAliasAnalysis.h>

//===----------------------------------------------------------------------===//
/// This class implements an LLVM module analysis pass.
///
class SillyPerlAnalysis : public llvm::AnalysisInfoMixin<SillyPerlAnalysis> {
public:
    explicit SillyPerlAnalysis() = default;
    ~SillyPerlAnalysis() = default;
    // Provide a unique key, i.e., memory address to be used by the LLVM's pass
    // infrastructure.
    static llvm::AnalysisKey Key;
    friend llvm::AnalysisInfoMixin<SillyPerlAnalysis>;

    // Specify the result type of this analysis pass.
    using Result = llvm::DenseSet<llvm::Instruction*>;

    // Analyze the bitcode/IR in the given LLVM module.
    Result run(llvm::Module &M, [[maybe_unused]] llvm::ModuleAnalysisManager &MAM);
};

//===----------------------------------------------------------------------===//
/// This class implements an LLVM module analysis pass.
///
struct PointerDetector {
    llvm::DenseSet<llvm::Value*> pointers;
    llvm::DenseSet<llvm::Value*> negatedPointers;
    // mutable because stupid me marked the PointerDetector as const everywhere 
    //  and i guess caches are kinda the only valid use case for mutable ??
    mutable llvm::DenseMap<llvm::Value*, std::pair<llvm::Value*, bool>> pointerToRealBase;

    enum ValueType { NEGATED_POINTER = -1, INTEGER = 0, POINTER = 1 };

    bool is_confirmed_pointer(llvm::Value* val) const { return pointers.contains(val); }
    std::optional<ValueType> is_unconfirmed_pointer(llvm::Value* val) const;
    llvm::Value* strip_pointer_casts(llvm::Value* pointer) const;
    std::pair<llvm::Value*, bool> find_real_base(llvm::Value *arithmetic) const;
    template<typename T>
    std::optional<ValueType> handle_unconfirmed_binaryOp(T* binaryOp) const;

    struct BinaryOpValueTypes {
        llvm::Value* pointerOperand;
        llvm::Value* nonPointerOperand;
    };
    std::optional<BinaryOpValueTypes> findBinaryOpValueTypes(llvm::BinaryOperator* binaryOp) const;

    std::optional<llvm::APInt> findConstantOffset(llvm::GEPOperator* gep) const;
    std::optional<llvm::APInt> findConstantOffset(llvm::BinaryOperator* binaryOp) const;

    PointerDetector(llvm::Module &M, llvm::ModuleAnalysisManager &MAM);
    
private:
    llvm::Module& module;
    llvm::ModuleAnalysisManager& MAM;

    void identify_start_pointers(llvm::Module& module);
    void mark_pointer_origins(llvm::Value* pointer);
    template<typename T>
    std::optional<llvm::Value*> mark_binaryOp_origins(T* binaryOp, llvm::SmallVector<std::pair<llvm::Value *, ValueType>>& toMark);
    void mark_pointer_uses(llvm::Value* pointer);
    void mark_castOp_use(llvm::Value* castOp);
    template<typename T>
    void mark_binaryOp_use(T* binaryOp);
    void mark_actual_vs_formal_args(llvm::Module& module);
    void mark_value(llvm::Value*, ValueType status);
    bool postDominates(llvm::Instruction* evidenceOfPointerUse, llvm::Value* pointer);
};

class PointerDetectionAnalysis : public llvm::AnalysisInfoMixin<PointerDetectionAnalysis> {
public:

    explicit PointerDetectionAnalysis() = default;
    ~PointerDetectionAnalysis() = default;
    // Provide a unique key, i.e., memory address to be used by the LLVM's pass
    // infrastructure.
    static llvm::AnalysisKey Key;
    friend llvm::AnalysisInfoMixin<PointerDetectionAnalysis>;

    // Specify the result type of this analysis pass.
    using Result = PointerDetector;

    // Analyze the bitcode/IR in the given LLVM module.
    Result run(llvm::Module &M, [[maybe_unused]] llvm::ModuleAnalysisManager &MAM);
};
