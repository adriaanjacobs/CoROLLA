#include <corolla/reachability/reachingdefinitions.h>

#include <corolla/util.h>
#include <corolla/reachability/cfg_reachability.h>
#include <llvm/Analysis/AliasAnalysis.h>

llvm::AnalysisKey ReachingDefinitionsAnalysis::Key;

RDSInfo::RDSInfo(llvm::Module& module, llvm::ModuleAnalysisManager& MAM) : 
    module{module}, MAM{MAM}
{}

llvm::Value* RDSInfo::findDefForLoad(llvm::LoadInst* load, std::function<llvm::Value*(llvm::Value*)> stripPointerCasts) {
    auto& dataLayout = load->getModule()->getDataLayout();
    ASSERT_ELSE_UNKOWN(dataLayout.getTypeSizeInBits(load->getType()) == 64, load);

    // a makeshift quick and dirty intra-block definition analysis for this load, catches really trivial cases, especially on load/stores through globals
    auto stripPtrOperand = stripPointerCasts(load->getPointerOperand());
    llvm::Instruction* potDef = load;
    while ((potDef = potDef->getPrevNode())) {
        auto& aamanager = getFAM(module, MAM).getResult<llvm::AAManager>(*load->getFunction());
        if (auto storeInst = llvm::dyn_cast<llvm::StoreInst>(potDef)) {
            if (stripPointerCasts(storeInst->getPointerOperand()) == stripPtrOperand) { // as crazy as it looks, it actually happens in real code
                if (dataLayout.getTypeSizeInBits(storeInst->getValueOperand()->getType()) == 64) // otherwise this is a partial overwrite (<64) or an unanalyzable store of an aggregate (>64)
                    return storeInst->getValueOperand();
                else return nullptr;
            }
            
            // i want to use these alias analyses: BasicAA, GlobalsAA, CFLSteensAA
            auto aliasResult = aamanager.alias(storeInst->getPointerOperand(), load->getPointerOperand());
            // our strip_pointer_casts should really catch these mustAliases
            ASSERT_ELSE_UNKOWN(aliasResult != llvm::AliasResult::MustAlias, storeInst);
            bool couldAlias = aliasResult; // true if there is a possibility of aliasing (must, may & partial)
            if (couldAlias) // bail out if it can alias. better option is to push them back into an RDS
                return nullptr;
            // else continue the analysis
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

    auto aggregate = extractValue->getAggregateOperand();
 
    llvm::DenseSet<llvm::Instruction*> potDefinators;
    for (auto& use : aggregate->uses()) {
        auto user = use.getUser();
        if (auto insertValue = llvm::dyn_cast<llvm::InsertValueInst>(user)) {
            ASSERT_ELSE_UNKOWN(insertValue->getNumIndices() == 1, insertValue);
            if (insertValue->getIndices().front() == indexVal) { // if this is overwriting the same value
                ASSERT_ELSE_UNKOWN(insertValue->getAggregateOperand() == aggregate, insertValue); // otherwise recurse?
                potDefinators.insert(insertValue);
            }
        } else if (llvm::isa<llvm::ExtractValueInst, llvm::CallBase, llvm::StoreInst>(user)) {
            // ignore, can't modify the defined value at all
            //  the call & store copy the aggregate
        } else HANDLE_UNKOWN_VALUE(user);
    }

    // we've now found the potential insertvalue definers. However, two issues:
    //  1. correctness: the definition of the aggregate may also contain a viable value for this element (default value)
    //  2. precision: some of the potDefinators may not be the most recent, or may not even be able to reach the extractvalue

    // we address both issues at once by adding an instruction that represents the lifetime of the default value in the current function
    // we add this instruction to the potDefinators, and then comprehensively eliminate those that cannot reach the extractvalue without 
    //  passing through another potDefinator
    //  for insertvalues in other functions, we conservatively assume that they can always reach
    //      this always means that the extractvalue is global, and we are not about to figure an interprocedural happens-before relationship

    auto instRepresentingAggScope = [&] () {
        if (auto inst = llvm::dyn_cast<llvm::Instruction>(aggregate)) // call or smt
            return inst; // could i go a bit further here and try to find _its_ definer?
        else if (llvm::isa<llvm::Argument, llvm::GlobalVariable>(aggregate)) 
            // this just serves as a sentinel that we later recognize to signal that
            // the "default" value of the aggregate member 
            return &extractValue->getFunction()->getEntryBlock().front(); 
        else HANDLE_UNKOWN_VALUE(aggregate);
    } ();
    // by sheer chance, it's possible that the instRepresentingAggScope happens to be a relevant insertvalue
    // that would confuse our current implementation, ensure it doesnt happen
    assert(!potDefinators.contains(instRepresentingAggScope));
    potDefinators.insert(instRepresentingAggScope);

    // go through all possible definition sites and prune the ones that can definitely not deliver the current value
    //  either because it gets overwritten with another one
    //  or because it could never reach in the first place
    llvm::DenseSet<llvm::Instruction*> mostRecentDefiners;
    // handle the special case where the extractValue is the first instruction in the function (xalancbmk hits this)
    //  this confuses the rest of our implementation because isPotentiallyReachable is designed to be paranoid about to == from
    if (extractValue == &extractValue->getFunction()->getEntryBlock().front()) {
        ASSERT_ELSE_UNKOWN(instRepresentingAggScope == extractValue, aggregate); // otherwise what aggregate is this extractvalue getting??
        mostRecentDefiners.insert(extractValue);
    } else {
        auto& FAM = getFAM(module, MAM);
        auto& domTree = FAM.getResult<llvm::DominatorTreeAnalysis>(*extractValue->getFunction());
        auto& loopInfo = FAM.getResult<llvm::LoopAnalysis>(*extractValue->getFunction());
        llvm::DenseSet<llvm::Instruction*> exclusionSet{potDefinators};
        for (auto potDef : potDefinators) {
            bool dbg = exclusionSet.erase(potDef);
            assert(dbg);
            if (::isPotentiallyReachable(potDef, extractValue, exclusionSet, &domTree, &loopInfo))
                mostRecentDefiners.insert(potDef);
            exclusionSet.insert(potDef);
        }
    }
    ASSERT_ELSE_UNKOWN(!mostRecentDefiners.empty(), extractValue); // it's impossible that at least the instRepresentingAggScope can't reach it

    llvm::DenseSet<llvm::Value*> defs;
    for (auto definer : mostRecentDefiners) {
        if (definer == instRepresentingAggScope) {
            // this means the original "default" value of the aggregate could still be live at the extractvalue
            // we can continue here and try to find this default value
            //  but i dont want to right now
            return {};
        } else {
            auto insertValue = llvm::cast<llvm::InsertValueInst>(definer); // only the instRepresentingAggScope is not an insertvalue
            defs.insert(insertValue->getInsertedValueOperand());
        }
    }

    return defs;
}
