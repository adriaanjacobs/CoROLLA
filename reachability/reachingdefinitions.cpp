#include <llvm-util/reachability/reachingdefinitions.h>

#include <llvm-util/reachability/cfg_reachability.h>
#include <llvm-util/util.h>
#include <llvm-util/pointerdetection/pointerdetection.h>

llvm::AnalysisKey ReachingDefinitionsAnalysis::Key;

RDSInfo::RDSInfo(llvm::Module& module, llvm::ModuleAnalysisManager& MAM) : 
    module{module}, MAM{MAM}
{}

llvm::Value* RDSInfo::findDefForLoad(llvm::LoadInst* load, PointerDetector* pointerDetector) {
    ASSERT_ELSE_UNKOWN(load->getModule()->getDataLayout().getTypeSizeInBits(load->getType()) == 64, load);

    if (!pointerDetector)
        pointerDetector = MAM.getCachedResult<PointerDetectionAnalysis>(module);
    assert(pointerDetector);

    // a makeshift quick and dirty intra-block definition analysis for this load, catches really trivial cases
    auto stripPtrOperand = pointerDetector->strip_pointer_casts(load->getPointerOperand());
    llvm::Instruction* potDef = load;
    while ((potDef = potDef->getPrevNode())) {
        auto& aamanager = getFAM(module, MAM).getResult<llvm::AAManager>(*load->getFunction());
        if (auto storeInst = llvm::dyn_cast<llvm::StoreInst>(potDef)) {
            if (pointerDetector->strip_pointer_casts(storeInst->getPointerOperand()) == stripPtrOperand) {
                // as crazy as it looks, it actually happens in real code
                return storeInst->getValueOperand();                
            } else {
                // i want to use these alias analyses: BasicAA, GlobalsAA, CFLSteensAA
                auto aliasResult = aamanager.alias(storeInst->getPointerOperand(), load->getPointerOperand());
                // our strip_pointer_casts should really catch these mustAliases
                ASSERT_ELSE_UNKOWN(aliasResult != llvm::AliasResult::MustAlias, storeInst);
                bool couldAlias = aliasResult; // true if there is a possibility of aliasing (must, may & partial)
                if (couldAlias) // bail out if it can alias. better option is to push them back into an RDS
                    return nullptr;
                // else continue the analysis
            }
        } else if (auto callInst = llvm::dyn_cast<llvm::CallBase>(potDef)) {
            if (!aamanager.onlyReadsMemory(callInst)) // may def
                return nullptr;
            // else continue the analysis
        }
    }
    return nullptr;
}

llvm::DenseSet<llvm::Value*> RDSInfo::findDefsForExtractValue(llvm::ExtractValueInst* extractValue) {
    ASSERT_ELSE_UNKOWN(extractValue->getNumIndices() == 1, extractValue);
    auto indexVal = extractValue->getIndices().front();

    auto aggregate = extractValue->getAggregateOperand(); // most likely case: not defined by this function.
    auto instRepresentingAggScope = [&] () {
        if (auto inst = llvm::dyn_cast<llvm::Instruction>(aggregate))
            return inst; // i could go a bit further here and try to find _its_ definer, but meh
        else if (llvm::isa<llvm::Argument, llvm::GlobalVariable>(aggregate))
            return &extractValue->getFunction()->getEntryBlock().front();
        else HANDLE_UNKOWN_VALUE(aggregate);
    } ();

    llvm::DenseSet<llvm::InsertValueInst*> potDefinators;
    for (auto& use : aggregate->uses()) {
        auto user = use.getUser();
        if (auto insertValue = llvm::dyn_cast<llvm::InsertValueInst>(user)) {
            ASSERT_ELSE_UNKOWN(insertValue->getNumIndices() == 1, insertValue);
            if (insertValue->getIndices().front() == indexVal) {
                ASSERT_ELSE_UNKOWN(insertValue->getAggregateOperand() == aggregate, insertValue); // otherwise recurse?
                potDefinators.insert(insertValue);
            }
        } else if (llvm::isa<llvm::ExtractValueInst, llvm::CallBase, llvm::StoreInst>(user)) {
            // ignore, can't modify the defined value at all
        } else HANDLE_UNKOWN_VALUE(user);
    }

    auto& FAM = getFAM(module, MAM);
    auto& domTree = FAM.getResult<llvm::DominatorTreeAnalysis>(*extractValue->getFunction());
    auto& loopInfo = FAM.getResult<llvm::LoopAnalysis>(*extractValue->getFunction());

    llvm::DenseSet<llvm::Instruction*> exclusionSet;
    exclusionSet.insert(potDefinators.begin(), potDefinators.end());
    if (::isPotentiallyReachable(instRepresentingAggScope, extractValue, exclusionSet, &domTree, &loopInfo))
        return {};

    ASSERT_ELSE_UNKOWN(!potDefinators.empty(), extractValue);

    llvm::DenseSet<llvm::InsertValueInst*> directPreds;
    for (auto potDef : potDefinators) {
        bool dbg = exclusionSet.erase(potDef);
        assert(dbg);
        if (::isPotentiallyReachable(potDef, extractValue, exclusionSet, &domTree, &loopInfo))
            directPreds.insert(potDef);
        exclusionSet.insert(potDef);
    }

    llvm::DenseSet<llvm::Value*> defs;
    for (auto pred : directPreds)
        defs.insert(pred->getInsertedValueOperand());
    return defs;
}
