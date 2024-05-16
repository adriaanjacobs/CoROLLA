#pragma once

#include <cstdint>
#include <llvm/Support/HashBuilder.h>
#include <llvm/IR/PassManager.h>
#include <llvm/Analysis/LoopAnalysisManager.h>
#include <llvm/IR/Instructions.h>
#include <array>
#include <string>
#include <map>

#include <functional>
#include <llvm/IR/Operator.h>
#include <optional>
#include <llvm/Analysis/MustExecute.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/IR/Dominators.h>
#include <llvm/Analysis/PostDominators.h>
#include <llvm/Analysis/ScalarEvolutionExpressions.h>

#include <array>
#include <experimental/array>

void dumpModuleToFile(llvm::Module& module, std::string_view name);

llvm::Module* moduleOf(llvm::Value* val);

llvm::Function* functionOf(llvm::Value* val);

#define HANDLE_UNKOWN_VALUE(_val)                                                                               \
    do {                                                                                                        \
        auto evalval = (_val);                                                                                  \
        if (llvm::Module* _module__ = moduleOf(evalval)) {                                                          \
            dumpModuleToFile(*_module__, "currentmodule.atUnknownValue.debug.ll");                              \
            if (llvm::Function* _func__ = functionOf(evalval))                                                      \
                llvm::errs() << "In func: '" << _func__->getName() << "'\n";                                    \
        }                                                                                                       \
        llvm::errs() << "Unkown value type: \n";                                                                \
        llvm::errs() << "\t" << *evalval << "\n\n";                                                                 \
        llvm::errs() << "Is constant: " << (llvm::isa<llvm::Constant>(val) ? "yes" : "no") << "\n";             \
        llvm::errs() << "Is GlobalVariable: " << (llvm::isa<llvm::GlobalVariable>(evalval) ? "yes" : "no") << "\n"; \
        llvm::errs() << "Is ConstantData: " << (llvm::isa<llvm::ConstantData>(evalval) ? "yes" : "no") << "\n";     \
        llvm::errs() << "Is instruction: " << (llvm::isa<llvm::Instruction>(evalval) ? "yes" : "no") << "\n";       \
        llvm::errs() << "Is operator: " << (llvm::isa<llvm::Operator>(evalval) ? "yes" : "no") << "\n";             \
        llvm::errs().flush();                                                                                   \
        assert(!"Unkown instruction!");                                                                         \
    } while (false)

constexpr std::array scevTypesToString = std::experimental::make_array(
  "scConstant",
  "scTruncate",
  "scZeroExtend",
  "scSignExtend",
  "scAddExpr",
  "scMulExpr",
  "scUDivExpr",
  "scAddRecExpr",
  "scUMaxExpr",
  "scSMaxExpr",
  "scUMinExpr",
  "scSMinExpr",
  "scSequentialUMinExpr",
  "scPtrToInt",
  "scUnknown",
  "scCouldNotCompute"
);

#define PRINT_UNKOWN_SCEV(scev) \
    do {    \
        auto evalscev = (scev); \
        llvm::errs() << "Unkown scev with type '" << scevTypesToString[evalscev->getSCEVType()] << "':\n";   \
        llvm::errs() << "\t" << *evalscev << "\n";   \
    } while (false) 

#define HANDLE_UNKOWN_SCEV(scev) \
    do {    \
        PRINT_UNKOWN_SCEV(scev); \
        assert(!"Unknown SCEV type!");  \
    } while (false) 

#define ASSERT_ELSE_UNKOWN_SCEV(cond, scev)     \
    do {                                        \
        bool condVal = static_cast<bool>(cond); \
        if (!condVal) {                         \
            HANDLE_UNKOWN_SCEV(scev);           \
        }                                       \
    } while (false)

#define ASSERT_ELSE_UNKOWN(cond, val)           \
    do {                                        \
        bool condVal = static_cast<bool>(cond); \
        if (!condVal) {                         \
            HANDLE_UNKOWN_VALUE(val);           \
        }                                       \
    } while (false)

#define BREAKPOINT() \
    asm("int $3")

struct run_on_destruct {
    std::function<void()> func;
    run_on_destruct(auto func) : func{std::move(func)} {}
    ~run_on_destruct() { func(); }
};

#define CONCAT_(x,y) x##y
#define CONCAT(x,y) CONCAT_(x,y)
#define UNIQUE_VAR_NAME CONCAT(_unique_var_, __COUNTER__)
#define defer(block) run_on_destruct UNIQUE_VAR_NAME{[&] () -> void { block; }}

inline llvm::FunctionAnalysisManager& getFAM(llvm::Module& module, llvm::ModuleAnalysisManager& MAM) {
    return MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(module).getManager();
}

inline llvm::LoopAnalysisManager& getLAM(llvm::Function& function, llvm::FunctionAnalysisManager& FAM) {
    return FAM.getResult<llvm::LoopAnalysisManagerFunctionProxy>(function).getManager();
}

template<typename T>
inline llvm::raw_ostream& operator << (llvm::raw_ostream& OS, const std::optional<T>& optVal) {
    if (optVal.has_value())
        OS << optVal.value();
    else OS << "<empty optional>";
    return OS;
}

llvm::MustBeExecutedContextExplorer getMustBeExecutedContextExplorer(llvm::FunctionAnalysisManager& FAM, bool forward, bool backward);

enum struct DIRECTION { LOWER, UPPER };

template<DIRECTION DIR>
std::optional<llvm::APInt> getSignedSCEVLimit(const llvm::SCEV* scev, llvm::ScalarEvolution& SE) {
    using enum DIRECTION;
    auto range = SE.getSignedRange(scev);
    // heuristic to filter out the uncomputable ones
    if (scev->getSCEVType() != llvm::scCouldNotCompute) {
        if (DIR == UPPER && range.getSignedMax().slt(llvm::APInt::getSignedMaxValue(64)))
            return range.getSignedMax();
        if (DIR == LOWER && range.getSignedMin().sgt(llvm::APInt::getSignedMinValue(64)))
            return range.getSignedMin();
    }
    return std::nullopt;
}

llvm::Value* castToInt64Ty(llvm::Value* val, llvm::Instruction* insertBefore, llvm::StringRef name = "");

std::string getModuleHash(llvm::Module& module);

namespace llvm {
    template<typename T>
    struct DenseMapInfo<DenseSet<T*>> {
        static bool isEqual(const DenseSet<T*>& one, const DenseSet<T*>& other) {
            return one == other;
        }

        static DenseSet<T*> getTombstoneKey() {
            DenseSet<T*> ret;
            ret.insert((T*)~1);
            return ret;
        }

        static DenseSet<T*> getEmptyKey() {
            DenseSet<T*> ret;
            ret.insert((T*)-0);
            return ret;
        }

        static unsigned getHashValue(const DenseSet<T*>& ptrs) {
            unsigned accumulator = 0xDEADBEEFU;;
            for (auto ptr : ptrs) 
                accumulator = detail::combineHashValue(accumulator, DenseMapInfo<T*>::getHashValue(ptr));
            return accumulator;
        }
    };
}

namespace std {
    template<typename T>
    struct hash<llvm::DenseSet<T>> {
        size_t operator () (const llvm::DenseSet<T>& set) const {
            unsigned accumulator = 0xDEADBEEFU;;
            for (auto& el : set) 
                accumulator = llvm::detail::combineHashValue(accumulator, std::hash<T>{}(el));
            return accumulator;
        }
    };
}

#if MY_LLVM_VERSION == 13
namespace llvm {
    inline bool getIndexExpressionsFromGEP(ScalarEvolution &SE,
                                const GetElementPtrInst *GEP,
                                SmallVectorImpl<const SCEV *> &Subscripts,
                                SmallVectorImpl<int> &Sizes) {
        return SE.getIndexExpressionsFromGEP(GEP, Subscripts, Sizes);
    }
}
#else 
#include <llvm/Analysis/Delinearization.h>
#endif

#if MY_LLVM_VERSION == 13
#include <llvm/Passes/PassBuilder.h>
namespace llvm {
    using OptimizationLevel = PassBuilder::OptimizationLevel;
}
#endif

bool isCallTo(llvm::StringRef name, llvm::Instruction* requirer);

template<typename AnalysisT>
class AnalysisResultBuilder {
    llvm::Module& module;
    llvm::ModuleAnalysisManager& MAM;
    // need a container with stable iterators here
    std::map<uint64_t, AnalysisT> infos;
public:
    AnalysisResultBuilder(llvm::Module& module, llvm::ModuleAnalysisManager& MAM)
        : module{module}, MAM{MAM}
    {}

    template<typename ...Args>
    AnalysisT& getOrCreate(Args&& ...args) {
        auto argsAsArray = std::experimental::make_array(args...);
        static_assert(argsAsArray.size() <= 64);
        uint64_t hash = 0;
        for (uint i = 0; i < argsAsArray.size(); i++) {
            const auto arg = argsAsArray[i];
            hash |= (1UL << i);
        }
        auto it = infos.try_emplace(hash, module, MAM, std::forward<Args>(args)...).first;
        return it->second;
    }
};

/// Return the set of functions this call site is known to call. For direct
/// calls, the returned set contains the called function. For indirect calls,
/// this function collects known callees from !callees metadata, if present.
llvm::SmallVector<llvm::Function*> getKnownCallees(llvm::CallBase* call);

/*
    Returns an insertion point suitable for placing instrumentation after CallBase instructions.
    For invokes, returns the normal destination (where the return value makes sense)
*/
llvm::Instruction* normalInsertionPtAfter(llvm::Instruction* inst);

llvm::APInt findMinimumUnsignedValue(llvm::Value* val, llvm::Function* context, llvm::ModuleAnalysisManager& MAM);
