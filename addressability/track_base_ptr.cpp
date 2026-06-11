#include <corolla/addressability/addressability.h>

#include <corolla/util.h>
#include <corolla/pointerdetection/pointerdetection.h>

#include <llvm/Support/FormatVariadic.h>

BasePtrTracker::BasePtrTracker(std::function<BasePtrInfo(llvm::Value*)> findBasePtr, std::function<llvm::Value*(llvm::Value*)> insertAtBase) : 
    findBasePtr{findBasePtr}, insertAtBase{insertAtBase}
{}

BasePtrTracker::BasePtrTrackerInfo BasePtrTracker::trackBasePtr(llvm::Value* ptr) {
    auto [base, offseted] = findBasePtr(ptr);
    if (ptr == base)
        ASSERT_ELSE_UNKOWN(!offseted, ptr);

    if (auto it = cachedTrackers.find(base); it != cachedTrackers.end()) {
        auto [cachedBase, cachedBaseOffseted] = it->getSecond();
        // don't modify the cached entry
        bool combinedOffseted = offseted;
        if (cachedBaseOffseted.has_value() && cachedBaseOffseted.value())
            combinedOffseted = true;
        return {cachedBase, combinedOffseted};
    }

    // we only really have to do something special for phis and selects
    if (auto phi = llvm::dyn_cast<llvm::PHINode>(base)) {
        auto trackerPhi = llvm::PHINode::Create(
            phi->getType(), 
            phi->getNumIncomingValues(), 
            llvm::formatv("basetracker.{0}", phi->getName()), 
            phi->getNextNode()
        );
        // update the cache already so any circular references already use the correct pre-existing phitracker 
        //  (that is still under construction)
        // while we still haven't finalized the value, we do not fill in the isModified field yet
        cachedTrackers[phi] = {trackerPhi, std::nullopt};

        // i think this one should fail at some point no?
        ASSERT_ELSE_UNKOWN(llvm::pred_size(phi->getParent()) == phi->getNumIncomingValues(), phi); 

        // phis contain multiple duplicate entries for different edges from the same predecessor
        // if we naively find/insert their trackers and cast them to the correct value, we will
        //  inadvertently create a trackerphi that has different bitcast instructions of the same
        //  tracker for these duplicate entries
        // hence, we first deduplicate the phi incoming edges, insert the tracker once for each,
        //  then duplicate the trackerphi entries as necessary
        llvm::DenseMap<llvm::BasicBlock*, llvm::Value*> predToCastedTracker;
        bool anyTrackerIsModified = offseted;
        for (auto pred : llvm::predecessors(phi->getParent())) {
            if (!predToCastedTracker.count(pred)) {
                auto [trackerValue, trackerIsOffseted] = trackBasePtr(phi->getIncomingValueForBlock(pred));
                // cast to correct type. insert at end of predecessor to ensure it's defined for this phi
                //     the ifNecessary here avoids stupid issues with invokes where the types are never going to differ
                //     but unconditionally inserting a cast instruction makes it hard to choose where to do it
                predToCastedTracker[pred] = createBitOrPointerCastIfNecessary(trackerValue, phi->getType(), "", pred->getTerminator());
                // if any of the offset booleans are true, the result is true
                // if all of the offset booleans (have a value and) are false, the result is false
                // in every other case, the combined offset boolean is nullopt
                // the offset boolean can only be nullopt here if it is self-referential
                //  in which case, we know the self-referential part is non-modified, otherwise it would have returned true
                // so i think we can totally ignore nullopts, because they don't contribute anything
                //  if the rest agrees that it is modified, it's modified
                //  if the rest agrees that it's not modified, it's not modified
                if (trackerIsOffseted.has_value()) {
                    if (trackerIsOffseted.value() == true)
                        anyTrackerIsModified = true;
                }
            }
            auto castedTracker = predToCastedTracker[pred];
            trackerPhi->addIncoming(castedTracker, pred);
        }

        // we've completely analyzed the phi here, update the cache
        BasePtrTrackerInfo ret{trackerPhi, anyTrackerIsModified};
        cachedTrackers[phi] = ret;
        return ret;
    } else if (auto select = llvm::dyn_cast<llvm::SelectInst>(base)) {
        auto trackerSelect = llvm::SelectInst::Create(
            select->getCondition(), 
            select->getTrueValue(), // placeholder true and false values to construct the phi
            select->getFalseValue(), 
            llvm::formatv("basetracker.{0}", select->getName()),
            select->getNextNode()
        );
        // same caching story as phi, even though i dont think selects can be self-referential (?)
        cachedTrackers[select] = {trackerSelect, std::nullopt};

        auto [trackerIfTrue, offsetedIfTrue] = trackBasePtr(select->getTrueValue());
        trackerIfTrue = llvm::CastInst::CreateBitOrPointerCast(trackerIfTrue, select->getType(), "", trackerSelect);
        trackerSelect->setTrueValue(trackerIfTrue);

        auto [trackerIfFalse, offsetedIfFalse] = trackBasePtr(select->getFalseValue());
        trackerIfFalse = llvm::CastInst::CreateBitOrPointerCast(trackerIfFalse, select->getType(), "", trackerSelect);
        trackerSelect->setFalseValue(trackerIfFalse);

        // handle nullopt offseted booleans: these happen in case an operand comes from a phi which comes from the select
        //  in that case, it's the same story as for phi: 
        //      if we didnt observe any offsets in the recursive cycle (i.e. it's still nullopt), we don't wanna influence the decision
        bool anyOperandsModified = false;
        if (offsetedIfTrue.has_value() && offsetedIfTrue.value() == true)
            anyOperandsModified = true;
        if (offsetedIfFalse.has_value() && offsetedIfFalse.value() == true)
            anyOperandsModified = true;

        // we've completely analyzed the select here, update the cache
        BasePtrTrackerInfo ret{trackerSelect, offseted || anyOperandsModified};
        cachedTrackers[select] = ret;
        return ret;
    } else {
        // base case: we arrived at the baseptr (typically a load, call, extract*, argument, or something unanalyzable)
        // we still cache it so `insertAtBase` doesn't run more than once per base
        //  we use `nullopt` in the cache because different 
        BasePtrTrackerInfo ret{insertAtBase(base), offseted};
        cachedTrackers[base] = ret;
        cachedTrackers[base].isModified = std::nullopt; // we use `nullopt` in the cache because `isModified` does not depend on the base ptr
        return ret;
    }
}
