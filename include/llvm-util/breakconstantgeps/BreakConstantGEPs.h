//===- BreakConstantGEPs.h - Change constant GEPs into GEP instructions --- --//
//
//                          The SAFECode Compiler
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
// File was modified by A. Jacobs.
//
//===----------------------------------------------------------------------===//
//
// This pass changes all GEP constant expressions into GEP instructions.  This
// permits the rest of SAFECode to put run-time checks on them if necessary.
//
//===----------------------------------------------------------------------===//

#pragma once

#ifndef BREAKCONSTANTGEPS_H
#define BREAKCONSTANTGEPS_H

#include "llvm/Analysis/ProfileSummaryInfo.h"
#include "llvm/IR/PassManager.h"
#include <llvm/IR/Module.h>
#include <llvm/Pass.h>
#include <llvm/Transforms/Utils/UnifyFunctionExitNodes.h>
#include <llvm/Transforms/Utils/UnifyLoopExits.h>
#include <llvm/ADT/StringRef.h>

//
// Pass: BreakConstantGEPs
//
// Description:
//  This pass modifies a function so that it uses GEP instructions instead of
//  GEP constant expressions.
//
class BreakConstantGEPs : public llvm::ModulePass
{
private:
    // Private methods

    // Private variables

public:
    static char ID;
    BreakConstantGEPs() : ModulePass(ID) {}
    llvm::StringRef getPassName() const
    {
        return "Remove Constant GEP Expressions";
    }
    virtual bool runOnModule (llvm::Module & M);
    virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const
    {
        // This pass does not modify the control-flow graph of the function
        AU.setPreservesCFG();
    }
};

//===----------------------------------------------------------------------===//
/// This class implements an LLVM module transformation pass.
class BreakConstantGEPsPass : public llvm::PassInfoMixin<BreakConstantGEPsPass> {
public:
    explicit BreakConstantGEPsPass() = default;
    ~BreakConstantGEPsPass() = default;

    // Transform the bitcode/IR in the given LLVM module.
    llvm::PreservedAnalyses run(llvm::Module& module, llvm::ModuleAnalysisManager &MAM) {
        /// BreakConstantGEPs Pass
        std::unique_ptr<BreakConstantGEPs> p1 = std::make_unique<BreakConstantGEPs>();
        p1->runOnModule(module);
        return llvm::PreservedAnalyses::allInSet<llvm::CFGAnalyses>();
    }
};

#endif
