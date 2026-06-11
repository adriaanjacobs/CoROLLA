#pragma once

#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/Module.h>

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
