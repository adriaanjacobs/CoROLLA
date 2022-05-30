#pragma once

#include <cstdint>
#include <llvm/IR/PassManager.h>
#include <llvm/Analysis/LoopAnalysisManager.h>
#include <llvm/IR/Instructions.h>
#include <array>
#include <experimental/array>
#include <string>

#if 0
#ifndef BOOST_STACKTRACE_USE_BACKTRACE
    #define BOOST_STACKTRACE_USE_BACKTRACE
#endif

#include <boost/stacktrace.hpp>

#include <source_location>
#include <llvm/Support/raw_ostream.h>
#include <signal.h>

#define dbg_assert(expr) \
    if (!static_cast<bool>(expr)) { \
        llvm::outs().flush();   \
        llvm::outs().flush();   \
        std::cout.flush();  \
        std::cerr.flush();  \
        std::cerr << __FILE__ << ":" << __LINE__ << ": " << __func__ << ": Assertion `" << #expr << "` failed.\n"; \
        std::cerr << "Backtrace: \n";   \
        std::cerr << boost::stacktrace::stacktrace();   \
        std::cerr << std::endl; \
        raise(SIGABRT); \
    }
#endif

#include <functional>
#include <llvm/IR/Operator.h>
#include <optional>
#include <llvm/Analysis/MustExecute.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/IR/Dominators.h>
#include <llvm/Analysis/PostDominators.h>
#include <llvm/Analysis/ScalarEvolutionExpressions.h>

struct run_on_destruct {
    std::function<void()> func;
    run_on_destruct(auto func) : func{std::move(func)} {}
    ~run_on_destruct() { func(); }
};

#define HANDLE_UNKOWN_VALUE(val)                                    \
    do {        \
        llvm::outs() << "Unkown value type: \n";      \
        llvm::outs() << "\t" << *val << "\n\n";     \
        llvm::outs() << "Is constant: " << (llvm::isa<llvm::Constant>(val) ? "yes" : "no") << "\n"; \
        llvm::outs() << "Is GlobalVariable: " << (llvm::isa<llvm::GlobalVariable>(val) ? "yes" : "no") << "\n"; \
        llvm::outs() << "Is ConstantData: " << (llvm::isa<llvm::ConstantData>(val) ? "yes" : "no") << "\n"; \
        llvm::outs() << "Is instruction: " << (llvm::isa<llvm::Instruction>(val) ? "yes" : "no") << "\n"; \
        llvm::outs() << "Is operator: " << (llvm::isa<llvm::Operator>(val) ? "yes" : "no") << "\n"; \
        llvm::outs().flush(); \
        assert(!"Unkown instruction!");     \
    } while (false)

#define ASSERT_ELSE_UNKOWN(cond, val) \
    do {                                                \
        bool condVal = static_cast<bool>(cond);     \
        if (!condVal) {                                \
            HANDLE_UNKOWN_VALUE(val);               \
        }                                           \
    } while (false)

#define BREAKPOINT() \
    asm("int $3")

inline llvm::FunctionAnalysisManager& getFAM(llvm::Module& module, llvm::ModuleAnalysisManager& MAM) {
    return MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(module).getManager();
}

inline llvm::LoopAnalysisManager& getLAM(llvm::Function& function, llvm::FunctionAnalysisManager& FAM) {
    return FAM.getResult<llvm::LoopAnalysisManagerFunctionProxy>(function).getManager();
}

inline llvm::Function* functionOf(llvm::Value* val) {
    if (auto inst = llvm::dyn_cast<llvm::Instruction>(val))
        return inst->getFunction();
    else if (auto arg = llvm::dyn_cast<llvm::Argument>(val))
        return arg->getParent();
    else return nullptr;
}


template<typename T>
inline llvm::raw_ostream& operator << (llvm::raw_ostream& OS, const std::optional<T>& optVal) {
    if (optVal.has_value())
        OS << optVal.value();
    else OS << "<empty optional>";
    return OS;
}

inline llvm::MustBeExecutedContextExplorer getMustBeExecutedContentExplorer(llvm::FunctionAnalysisManager& FAM) {
    return llvm::MustBeExecutedContextExplorer(true, true, true, 
        [&] (const llvm::Function& func) -> const llvm::LoopInfo* { return &FAM.getResult<llvm::LoopAnalysis>(const_cast<llvm::Function&>(func)); },
        [&] (const llvm::Function& func) -> const llvm::DominatorTree* { return &FAM.getResult<llvm::DominatorTreeAnalysis>(const_cast<llvm::Function&>(func)); },
        [&] (const llvm::Function& func) -> const llvm::PostDominatorTree* { return &FAM.getResult<llvm::PostDominatorTreeAnalysis>(const_cast<llvm::Function&>(func)); }
    );
}

enum DIRECTION { LOWER, UPPER };

template<DIRECTION DIR>
std::optional<llvm::APInt> getSignedSCEVLimit(const llvm::SCEV* scev, llvm::ScalarEvolution& SE) {
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

inline llvm::Value* castToInt64Ty(llvm::Value* val, llvm::Instruction* insertBefore, llvm::StringRef name = "") {
    llvm::Type* int64Ty = llvm::Type::getInt64Ty(insertBefore->getModule()->getContext());

    if (val->getType()->isPointerTy()) {
        auto ptrToInt = llvm::PtrToIntInst::Create(llvm::CastInst::PtrToInt, val, int64Ty, name, insertBefore);
        val = ptrToInt;
    }

    assert(val->getType()->isIntegerTy());
    assert(insertBefore->getModule()->getDataLayout().getTypeSizeInBits(val->getType()).getFixedSize() == 64);
    return val;
}

inline std::string getModuleHash(llvm::Module& module) {
    size_t bbcount = 0;
    size_t instcount = 0;
    for (auto& func : module)
        for (auto& bb : func) {
            bbcount++;
            for (auto& inst : bb)
                instcount++;
        }
    
    return module.getSourceFileName() + "_" + module.getTargetTriple() + "_" + std::to_string(module.size()) + "_" + std::to_string(bbcount) + "_" + std::to_string(instcount);
}

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