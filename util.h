#pragma once

#include <cstdint>
#include <llvm/Support/HashBuilder.h>
#include <llvm/IR/PassManager.h>
#include <llvm/Analysis/LoopAnalysisManager.h>
#include <llvm/IR/Instructions.h>
#include <array>
#include <string>
#include <map>

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

#include <array>
#include <experimental/array>

inline void dumpModuleToFile(llvm::Module& module, std::string_view name) {
    std::error_code code;
    llvm::raw_fd_ostream file(name, code);
    assert(code.value() == 0);
    module.print(file, nullptr);
}

// adapted from 'getModuleFromVal' in LLVM's AsmWriter.cpp
inline llvm::Module* moduleOf(llvm::Value* val) {
    using namespace llvm;
    if (auto arg = dyn_cast<Argument>(val))
        return arg->getParent() ? arg->getParent()->getParent() : nullptr;
    
    if (auto bb = dyn_cast<BasicBlock>(val))
        return bb->getParent() ? bb->getParent()->getParent() : nullptr;
    
    if (auto inst = dyn_cast<Instruction>(val)) {
        auto function = inst->getParent() ? inst->getFunction() : nullptr;
        return function ? function->getParent() : nullptr;
    }
    
    if (auto globul = dyn_cast<GlobalValue>(val))
        return globul->getParent();
    
    if (auto mtdata = dyn_cast<MetadataAsValue>(val)) {
        for (auto user : mtdata->users())
        if (isa<Instruction>(user))
            if (auto M = moduleOf(user))
                return M;
        return nullptr;
    }
    
    return nullptr;
}

inline llvm::Function* functionOf(llvm::Value* val) {
    if (auto inst = llvm::dyn_cast<llvm::Instruction>(val))
        return inst->getFunction();
    else if (auto arg = llvm::dyn_cast<llvm::Argument>(val))
        return arg->getParent();
    else return nullptr;
}

#define HANDLE_UNKOWN_VALUE(val)                                                                                \
    do {                                                                                                        \
        if (auto _module__ = moduleOf(val)) {                                                                   \
            auto filename = "currentmodule.atUnknownValue.debug.ll";                                            \
            dumpModuleToFile(*_module__, filename);                                                             \
            llvm::outs() << "Printed module to '" << filename << "' for debugging!\n";                          \
            if (auto _func__ = functionOf(val))                                                                 \
                llvm::outs() << "In func: '" << _func__->getName() << "'\n";                                    \
        }                                                                                                       \
        llvm::outs() << "Unkown value type: \n";                                                                \
        llvm::outs() << "\t" << *val << "\n\n";                                                                 \
        llvm::outs() << "Is constant: " << (llvm::isa<llvm::Constant>(val) ? "yes" : "no") << "\n";             \
        llvm::outs() << "Is GlobalVariable: " << (llvm::isa<llvm::GlobalVariable>(val) ? "yes" : "no") << "\n"; \
        llvm::outs() << "Is ConstantData: " << (llvm::isa<llvm::ConstantData>(val) ? "yes" : "no") << "\n";     \
        llvm::outs() << "Is instruction: " << (llvm::isa<llvm::Instruction>(val) ? "yes" : "no") << "\n";       \
        llvm::outs() << "Is operator: " << (llvm::isa<llvm::Operator>(val) ? "yes" : "no") << "\n";             \
        llvm::outs().flush();                                                                                   \
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

#define HANDLE_UNKOWN_SCEV(scev) \
    do {    \
        llvm::outs() << "Unkown scev with type '" << scevTypesToString[scev->getSCEVType()] << "':\n";   \
        llvm::outs() << "\t" << *scev << "\n";   \
        assert(!"Unknown SCEV type!");  \
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

inline llvm::MustBeExecutedContextExplorer getMustBeExecutedContextExplorer(llvm::FunctionAnalysisManager& FAM, bool forward, bool backward) {
    return llvm::MustBeExecutedContextExplorer(true, forward, backward, 
        [&] (const llvm::Function& func) -> const llvm::LoopInfo* { return &FAM.getResult<llvm::LoopAnalysis>(const_cast<llvm::Function&>(func)); },
        [&] (const llvm::Function& func) -> const llvm::DominatorTree* { return &FAM.getResult<llvm::DominatorTreeAnalysis>(const_cast<llvm::Function&>(func)); },
        [&] (const llvm::Function& func) -> const llvm::PostDominatorTree* { return &FAM.getResult<llvm::PostDominatorTreeAnalysis>(const_cast<llvm::Function&>(func)); }
    );
}

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
    uint64_t hash_value = 0xDEADBEEF;
    for (auto& func : module)
        for (auto& bb : func) {
            bbcount++;
            for (auto& inst : bb) {
                instcount++;
                hash_value ^= inst.getOpcode();
            }
        }
    
    return std::to_string(llvm::hash_value(module.getSourceFileName())) + "_" + module.getTargetTriple() + "_" + std::to_string(module.size()) + "_" + std::to_string(bbcount) + "_" + std::to_string(instcount) + "_" + std::to_string(hash_value);
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

inline bool isCallTo(llvm::StringRef name, llvm::Instruction* requirer) {
    auto call = llvm::dyn_cast<llvm::CallBase>(requirer);
    if (!call)
        return false;
    if (auto calledFunc = call->getCalledFunction(); calledFunc && calledFunc->getName() == name)
        return true;
    return false;
}

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

