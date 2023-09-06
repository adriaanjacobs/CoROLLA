#pragma once

#include "util.h"
#include <clang/Basic/LangStandard.h>


std::unique_ptr<llvm::Module> compileIntoBitcode(std::string_view path, clang::Language lang, std::string_view targetTriple, llvm::LLVMContext* context);
llvm::DenseSet<llvm::Function*> compileAndLinkIntoModule(std::string_view code, llvm::Module& module);


