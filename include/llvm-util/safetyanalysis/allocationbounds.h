#pragma once

#include <llvm/IR/PassManager.h>
#include <llvm/IR/Value.h>

#include <optional>

bool isNonWrapperAllocSite(llvm::Value* val);

std::optional<std::pair<llvm::APInt, llvm::APInt>> findMinimumAllocBounds(llvm::Value* allocInstr, llvm::Module& module, llvm::ModuleAnalysisManager& MAM);
