#include <llvm/Pass.h>
#include <llvm/Passes/PassBuilder.h>

struct PointerDetector;

class ReachingDefinitionsAnalysis : public llvm::AnalysisInfoMixin<ReachingDefinitionsAnalysis> {
public:
    static llvm::AnalysisKey Key;

    struct RDSInfo {
        llvm::Module& module;
        llvm::ModuleAnalysisManager& MAM;
        RDSInfo(llvm::Module&, llvm::ModuleAnalysisManager&);

        llvm::Value* findDefForLoad(llvm::LoadInst* load, PointerDetector* pointerDetector = nullptr);
        llvm::DenseSet<llvm::Value*> findDefsForExtractValue(llvm::ExtractValueInst* extractValue);
    };

    using Result = RDSInfo;

    RDSInfo run(llvm::Module& module, llvm::ModuleAnalysisManager& MAM) {
        return RDSInfo{module, MAM};
    }
};

using RDSInfo = ReachingDefinitionsAnalysis::RDSInfo;
