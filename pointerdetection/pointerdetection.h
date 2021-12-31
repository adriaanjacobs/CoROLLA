#pragma once

#include "llvm/IR/Instructions.h"
#include <llvm/Pass.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Operator.h>
#include <llvm/Support/Casting.h>
#include <optional>
#include <mpk_instrument/pass.h>
#include <llvm/Analysis/LazyBlockFrequencyInfo.h>
#include <llvm/Analysis/BasicAliasAnalysis.h>

//===----------------------------------------------------------------------===//
/// This class implements an LLVM module analysis pass.
///
class PointerDetectionAnalysis : public llvm::AnalysisInfoMixin<PointerDetectionAnalysis> {
public:

    struct Detector {
        llvm::DenseSet<llvm::Value*> pointers;
        llvm::DenseSet<llvm::Value*> negatedPointers;

        enum ValueType { NEGATED_POINTER = -1, INTEGER = 0, POINTER = 1 };

        void identify_start_pointers(llvm::Module& module);
        void mark_pointer_origins(const llvm::DataLayout& dataLayout, llvm::Value* pointer);
        void mark_pointer_uses(const llvm::DataLayout& dataLayout, llvm::Value* pointer);
        void mark_actual_vs_formal_args(llvm::Module& module);
        void mark_value(const llvm::DataLayout& dataLayout, llvm::Value*, ValueType status);
        bool is_confirmed_pointer(llvm::Value* val) const { return pointers.contains(val); }
        std::optional<ValueType> is_unconfirmed_pointer(const llvm::DataLayout& dataLayout, llvm::Value* val) const;

        struct BinaryOpValueTypes {
            llvm::Value* pointerOperand;
            llvm::Value* nonPointerOperand;
        };

        std::optional<BinaryOpValueTypes> findBinaryOpValueTypes(llvm::BinaryOperator* binaryOp);

        Detector(llvm::Module &M, llvm::ModuleAnalysisManager &MAM);
        
        static llvm::Function* functionOf(llvm::Value* val);
    private:
        llvm::Module& module;
        llvm::ModuleAnalysisManager& MAM;
    };

    explicit PointerDetectionAnalysis() = default;
    ~PointerDetectionAnalysis() = default;
    // Provide a unique key, i.e., memory address to be used by the LLVM's pass
    // infrastructure.
    static llvm::AnalysisKey Key;
    friend llvm::AnalysisInfoMixin<PointerDetectionAnalysis>;

    // Specify the result type of this analysis pass.
    using Result = Detector;

    // Analyze the bitcode/IR in the given LLVM module.
    Result run(llvm::Module &M, [[maybe_unused]] llvm::ModuleAnalysisManager &MAM);
};

using PointerDetector = PointerDetectionAnalysis::Detector;