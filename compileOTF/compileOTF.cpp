#include <corolla/compileOTF/compileOTF.h>

#include <clang/AST/ASTContext.h>
#include <clang/AST/ASTConsumer.h>
#include <clang/Basic/DiagnosticOptions.h>
#include <clang/Basic/Diagnostic.h>
#include <clang/Basic/FileManager.h>
#include <clang/Basic/FileSystemOptions.h>
#include <clang/Basic/LangOptions.h>
#include <clang/Basic/SourceManager.h>
#include <clang/Basic/TargetInfo.h>
#include <clang/CodeGen/CodeGenAction.h>
#include <clang/Frontend/CompilerInstance.h>
#include <clang/Frontend/CompilerInvocation.h>
#include <clang/Frontend/TextDiagnosticPrinter.h>
#include <clang/Frontend/FrontendOptions.h>
#include <clang/Lex/HeaderSearch.h>
#include <clang/Lex/HeaderSearchOptions.h>
#include <clang/Lex/Preprocessor.h>
#include <clang/Lex/PreprocessorOptions.h>
#include <clang/Parse/ParseAST.h>
#include <clang/Sema/Sema.h>

#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Support/Host.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/Linker/Linker.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/Analysis/LazyCallGraph.h>
#include <llvm/Analysis/CGSCCPassManager.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Passes/OptimizationLevel.h>
#include <llvm/Analysis/AliasAnalysis.h>

#include <fstream>
#include <sstream>
#include <unordered_set>

// WE DONT NEED TO SEPARATE ANY OF THIS OUT, WE JUST HAVE TO LOAD THE .BC FILE FOR EXTAPI
std::unique_ptr<llvm::Module> compileIntoBitcode(std::string_view path, clang::Language lang, std::string_view targetTriple, llvm::LLVMContext* context) {
    clang::DiagnosticOptions* diagnosticOptions = new clang::DiagnosticOptions();
    clang::TextDiagnosticPrinter* textDiagnosticPrinter = new clang::TextDiagnosticPrinter(llvm::outs(), diagnosticOptions);
 
    clang::DiagnosticsEngine* diagnosticsEngine = new clang::DiagnosticsEngine(nullptr, diagnosticOptions, textDiagnosticPrinter, false);
 
    clang::CompilerInstance compilerInstance;
    auto& compilerInvocation = compilerInstance.getInvocation();

    std::stringstream argBuilder;
    argBuilder << "-triple=" << targetTriple;
    std::string args = argBuilder.str();

    bool success = clang::CompilerInvocation::CreateFromArgs(compilerInvocation, {args.c_str()}, *diagnosticsEngine);
    assert(success);

    auto& targetOptions = compilerInvocation.getTargetOpts();
    targetOptions.Triple = targetTriple;
    auto& frontEndOptions = compilerInvocation.getFrontendOpts();
    frontEndOptions.Inputs.clear();
    frontEndOptions.Inputs.push_back(clang::FrontendInputFile(path, lang));
    auto& codeGenOptions = compilerInvocation.getCodeGenOpts();
    codeGenOptions.OpaquePointers = false; 
    assert(codeGenOptions.OpaquePointers == false);

    compilerInstance.createDiagnostics(textDiagnosticPrinter, false);
    assert(codeGenOptions.OpaquePointers == false);

    std::unique_ptr<clang::CodeGenAction> action = std::make_unique<clang::EmitLLVMOnlyAction>(context);
    assert(action);

    assert(codeGenOptions.OpaquePointers == false);
    success = compilerInstance.ExecuteAction(*action);
    assert(success && "Compilation failed!");
    auto bufferModule = action->takeModule();
    assert(bufferModule);
    return bufferModule;
}

llvm::DenseSet<llvm::Function*> compileAndLinkIntoModule(std::string_view code, llvm::Module& module) {
    // write the source code to a temporary file because the clang frontend can only parse files I think
    std::stringstream tempFileNameSS;
    tempFileNameSS << tempnam("/tmp", "OTFsc");
    tempFileNameSS << "_tempOTFsource_";
    tempFileNameSS << getModuleHash(module);
    tempFileNameSS << ".c";
    auto tempFileName = tempFileNameSS.str();

    std::ofstream sourceFile(tempFileName, std::ofstream::out|std::ofstream::trunc);
    sourceFile << code;
    sourceFile.close();
    
    auto bufferModule = compileIntoBitcode(tempFileName, clang::Language::C, module.getTargetTriple(), &module.getContext());

    // verify that it's not an opaque pointer module
    for (auto& func : *bufferModule)
        for (auto& bb : func)
            for (auto& inst : bb)
                if (auto load = llvm::dyn_cast<llvm::LoadInst>(&inst))
                    assert(!load->getPointerOperand()->getType()->isOpaquePointerTy());
    assert(module.getContext().hasSetOpaquePointersValue());
    module.getContext().setOpaquePointers(false);

    // Create the analysis managers.
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager bufferMAM;

    // Create the new pass manager builder.
    // Take a look at the PassBuilder constructor parameters for more
    // customization, e.g. specifying a TargetMachine or various debugging
    // options.
    llvm::PassBuilder PB;

    // Make sure to use the default alias analysis pipeline, otherwise we'll end
    // up only using a subset of the available analyses.
    // to change the alias analysis, i think i can change this to DSA or something.
    FAM.registerPass([&] { return PB.buildDefaultAAPipeline(); });

    // Register all the basic analyses with the managers.
    PB.registerModuleAnalyses(bufferMAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, bufferMAM);

    llvm::ModulePassManager MPM = PB.buildPerModuleDefaultPipeline(llvm::OptimizationLevel::O2);
    MPM.run(*bufferModule, bufferMAM); // optimize my boy

    llvm::DenseSet<llvm::Function*> functionsToRemove;
    for (auto& defFunc : *bufferModule) {
        if (defFunc.isDeclaration()) // we're only interested in definitions
            continue;

        auto funcInModule = [&] () -> llvm::Function* {
            for (auto& func : module)
                if (func.getName() == defFunc.getName())
                    return &func;
            return nullptr;
        } ();

        if (!funcInModule) {
            // insert it, other things we link may need it
        } else if (!funcInModule->isDeclaration()) {
            // do not override the custom definition of the module
            functionsToRemove.insert(&defFunc);
        } else {
            assert(funcInModule->isDeclaration());
            // the real module contains the decl for this function and uses it
            assert(funcInModule->getNumUses() != 0);
            // definitely insert it
        }
    }

    if (!functionsToRemove.empty()) {
        llvm::outs() << "Not going to insert the following definitions:\n";
        for (auto func : functionsToRemove) {
            llvm::outs() << "\t" << func->getName() << "\n";  
            func->eraseFromParent();
        }
    }

    std::unordered_set<std::string> linkedInNames;
    for (auto& func : *bufferModule)
        if (!func.isDeclaration())
            linkedInNames.insert(func.getName().str());

    bool error = llvm::Linker::linkModules(module, std::move(bufferModule));
    assert(!error && "Linking module failed!");

    llvm::DenseSet<llvm::Function*> linkedInFunctions;
    for (auto& func : module) {
        if (linkedInNames.contains(func.getName().str())) 
            linkedInFunctions.insert(&func);
    }

    if (!linkedInFunctions.empty()) {
            llvm::outs() << "Linked in the following definitions:\n";
        for (auto func : linkedInFunctions) {
            llvm::outs() << "\t'" << func->getName() << "'\n";
        }
    }

    llvm::outs() << "Linked helpers into module, instrumenting now!\n";
    return linkedInFunctions;
}