#include <llvm-util/util.h>

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

void dumpModuleToFile(llvm::Module& module, std::string_view name) {
    std::error_code code;
    llvm::raw_fd_ostream file(name, code);
    assert(code.value() == 0);
    module.print(file, nullptr);
    llvm::outs() << "Dumped module to '" << name << "' for debugging.\n";
}

// adapted from 'getModuleFromVal' in LLVM's AsmWriter.cpp
llvm::Module* moduleOf(llvm::Value* val) {
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

llvm::Function* functionOf(llvm::Value* val) {
    assert(val);
    if (auto inst = llvm::dyn_cast<llvm::Instruction>(val)) {
        if (!inst->getParent())
            llvm::outs() << *inst << "\n";
        assert(inst->getParent());
        assert(inst->getParent()->getParent());
        return inst->getFunction();
    } else if (auto arg = llvm::dyn_cast<llvm::Argument>(val))
        return arg->getParent();
    else return nullptr;
}

llvm::MustBeExecutedContextExplorer getMustBeExecutedContextExplorer(llvm::FunctionAnalysisManager& FAM, bool forward, bool backward) {
    return llvm::MustBeExecutedContextExplorer(true, forward, backward, 
        [&] (const llvm::Function& func) -> const llvm::LoopInfo* { return &FAM.getResult<llvm::LoopAnalysis>(const_cast<llvm::Function&>(func)); },
        [&] (const llvm::Function& func) -> const llvm::DominatorTree* { return &FAM.getResult<llvm::DominatorTreeAnalysis>(const_cast<llvm::Function&>(func)); },
        [&] (const llvm::Function& func) -> const llvm::PostDominatorTree* { return &FAM.getResult<llvm::PostDominatorTreeAnalysis>(const_cast<llvm::Function&>(func)); }
    );
}

llvm::Value* castToInt64Ty(llvm::Value* val, llvm::Instruction* insertBefore, llvm::StringRef name) {
    llvm::Type* int64Ty = llvm::Type::getInt64Ty(insertBefore->getModule()->getContext());

    if (val->getType()->isPointerTy()) {
        auto ptrToInt = llvm::PtrToIntInst::Create(llvm::CastInst::PtrToInt, val, int64Ty, name, insertBefore);
        val = ptrToInt;
    }

    assert(val->getType()->isIntegerTy());
    assert(insertBefore->getModule()->getDataLayout().getTypeSizeInBits(val->getType()).getFixedSize() == 64);
    return val;
}

std::string getModuleHash(llvm::Module& module) {
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

bool isCallTo(llvm::StringRef name, llvm::Instruction* requirer) {
    auto call = llvm::dyn_cast<llvm::CallBase>(requirer);
    if (!call)
        return false;
    if (auto calledFunc = call->getCalledFunction(); calledFunc && calledFunc->getName() == name)
        return true;
    return false;
}

/// Return the set of functions this call site is known to call. For direct
/// calls, the returned set contains the called function. For indirect calls,
/// this function collects known callees from !callees metadata, if present.
llvm::SmallVector<llvm::Function*> getKnownCallees(llvm::CallBase* call) {
    llvm::SmallVector<llvm::Function*> callees;

    if (auto func = call->getCalledFunction()) {
        // If the call site is direct, just add the called function to the set.
        callees.push_back(func);
        return callees;
    }

    if (auto node = call->getMetadata(llvm::LLVMContext::MD_callees)) {
        // Otherwise, if the call site is indirect, collect the known callees from
        // !callees metadata if present.
        for (const auto& operand : node->operands())
            if (auto *MDConstant = llvm::mdconst::extract_or_null<llvm::Constant>(operand))
                callees.push_back(cast<llvm::Function>(MDConstant));
    }

    return callees;
}

/*
    Returns an insertion point suitable for placing instrumentation after CallBase instructions.
    For invokes, returns the normal destination (where the return value makes sense)
*/
llvm::Instruction* normalInsertionPtAfter(llvm::Instruction* inst) {
    if (auto invoke = llvm::dyn_cast<llvm::InvokeInst>(inst)) {
        return &*invoke->getNormalDest()->getFirstInsertionPt();
    } else {
        ASSERT_ELSE_UNKOWN(inst->getNextNode(), inst);
        return inst->getNextNode();
    }
}

llvm::APInt findMinimumUnsignedValue(llvm::Value* val, llvm::Function* context, llvm::ModuleAnalysisManager& MAM) {
    if (auto constantInt = llvm::dyn_cast<llvm::ConstantInt>(val)) {
        return constantInt->getValue();
    } else {
        assert(context);
        auto& scev = getFAM(*context->getParent(), MAM).getResult<llvm::ScalarEvolutionAnalysis>(*context);
        auto sizeScev = scev.getSCEV(val);
        return scev.getUnsignedRangeMin(sizeScev);
    }
}

