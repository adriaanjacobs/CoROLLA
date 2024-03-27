#include <llvm-util/safetyanalysis/pass.h>

#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Analysis/CGSCCPassManager.h>
#include <llvm/Analysis/AliasAnalysis.h>

// We could, of course, also compile the above code into a shared object library
// that we can then use as a plugin for LLVM's optimizer 'opt'. But instead,
// here we are going the full do-it-yourself route and set up everything
// ourselves.
int main(int argc, char **argv) {
if (argc != 3) {
        llvm::outs() << "Usage: " << argv[0] << " <IR file> <output file>\n";
        return 1;
    }

    std::error_code code;
    llvm::raw_fd_ostream outputFile(argv[2], code);
    assert(code.value() == 0);

    // Parse an LLVM IR file.
    llvm::SMDiagnostic Diag;
    llvm::LLVMContext CTX;
    std::unique_ptr<llvm::Module> module = llvm::parseIRFile(argv[1], Diag, CTX);

    // Check if the module is valid.
    bool BrokenDbgInfo = false;
    if (llvm::verifyModule(*module, &llvm::outs(), &BrokenDbgInfo)) {
        llvm::outs() << "error: invalid module\n";
        assert(false);
    }
    if (BrokenDbgInfo) {
        llvm::outs() << "caution: debug info is broken\n";
    }

    // Create the analysis managers.
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;

    // Create the new pass manager builder.
    llvm::PassBuilder PB;

    // Make sure to use the default alias analysis pipeline, otherwise we'll end
    // up only using a subset of the available analyses.
    // to change the alias analysis, i think i can change this to DSA or something.
    FAM.registerPass([&] { return PB.buildDefaultAAPipeline(); });

    // Register all the basic analyses with the managers.
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    // Register our analyses
    MemAccessInstrumentator::registerAnalyses(MAM);

    llvm::ModulePassManager MPM;
    IsInBoundsAnalysis::addPassesAround<MemAccessInstrumentator>(MPM);
    // our own instrumentation
    MPM.addPass(MemAccessInstrumentator{});
    // Just to be sure that none of the passes messed up the module.
    MPM.addPass(llvm::VerifierPass{});
    
    MPM.run(*module, MAM);
    
    module->print(outputFile, nullptr);
    return 0;
}
