#include <llvm-utils/instrpointoptimization/dominationpruning.h>

#include <llvm-utils/reachability/cfg_reachability.h>

bool pruneDominatedChecks(
    llvm::DenseMap<InstrumentationPoint*, llvm::DenseSet<llvm::Use*>>& pointToUses, 
    std::function<llvm::Value*(llvm::Value*)> stripPointerCasts,
    llvm::DominatorTree& DT,
    llvm::LoopInfo& LI
) {
    bool change = false;
    llvm::DenseMap<llvm::Value*, llvm::DenseSet<InstrumentationPoint*>> ptrToPoints;
    for (auto& [point, _] : pointToUses) 
        ptrToPoints[stripPointerCasts(point->pointerOperand)].insert(point);
    for (auto& [_, samePtrPoints] : ptrToPoints) {
        // first, we de-duplicate same points in same place
        //  it's possible that the summarization transformation resulted in multiple of the same points at the same location
        //  fix up places where that happened
        llvm::DenseMap<llvm::Instruction*, llvm::DenseSet<InstrumentationPoint*>> insertBfToPoints;
        for (auto point : samePtrPoints)
            insertBfToPoints[point->insertBefore].insert(point);
        
        for (auto& [insertBefore, sameBfPoints] : insertBfToPoints) {
            // all these points share the same insertBf and pointerOperand!
            // we pick one point and let it describe all other uses
            //  we can't delete range checks. if possible, we pick a range check. if there's multiple range checks, pick one but don't delete the others
            //  if there's no range checks, we pick a random non-range point and move on
            llvm::DenseSet<InstrumentationPoint*> checksToKeep;
            for (auto& point : sameBfPoints)
                if (point->isRangeCheck())
                    checksToKeep.insert(point);
            
            auto singlePoint = [&, &points = sameBfPoints] () -> InstrumentationPoint* {
                if (!checksToKeep.empty())
                    return *checksToKeep.begin(); // using a range check
                assert(points.size() > 0);
                auto firstNonRangeCheck = *points.begin();
                checksToKeep.insert(firstNonRangeCheck);
                return firstNonRangeCheck;
            } ();

            assert(checksToKeep.size() >= 1);

            for (auto it = sameBfPoints.begin(); it != sameBfPoints.end();) {
                if (!checksToKeep.contains(*it)) {
                    // erase this one
                    assert(pointToUses.count(*it));
                    auto usesDescribed = pointToUses[*it];
                    assert(pointToUses.count(singlePoint));
                    pointToUses[singlePoint].insert(usesDescribed.begin(), usesDescribed.end());
                    pointToUses.erase(*it);
                    samePtrPoints.erase(*it);
                    sameBfPoints.erase(it);
                    change = true;
                };
                it++;
            }

            assert(sameBfPoints.size() == checksToKeep.size());
        }

        // now, no location contains multiple of the same checks
        //  we move on to more general split-domination pruning
        //  is it possible to reach each point from the function entry without passing through any of the other points?
        llvm::DenseSet<llvm::Instruction*> exclusionSet;
        // handle the edge case where some of the points are at the function start
        //  our reachability query cannot handle a from that is also in the exclusionSet
        auto funcStart = &(*samePtrPoints.begin())->insertBefore->getFunction()->getEntryBlock().front();
        llvm::DenseSet<InstrumentationPoint*> toRemove;
        for (auto& point : samePtrPoints) {
            if (point->insertBefore == funcStart) {
                if (point->isRangeCheck()) {
                    // clear all other points
                    toRemove.insert(samePtrPoints.begin(), samePtrPoints.end());
                    auto dbg = toRemove.erase(point);
                    assert(dbg);
                } else {
                    // clear all non-range points
                    for (auto otherpoint : samePtrPoints)
                        if (!otherpoint->isRangeCheck() && otherpoint != point)
                            toRemove.insert(otherpoint);
                }
            }
        }

        for (auto point : toRemove) {
            samePtrPoints.erase(point);
            pointToUses.erase(point);
            change = true;
        }

        // now do the split-domination pruning
        for (auto point : samePtrPoints)
            exclusionSet.insert(point->insertBefore);
        
        // check reachability edge case: if the funcStart is in the exclusionSet, it trivially dominates all other points
        //  we should have handled this before
        if (!exclusionSet.contains(funcStart)) {
            for (auto point : samePtrPoints) {
                // range checks cannot be deleted by single-pointer checks, even when dominated
                //  however, range checks that start on the same base can still help eliminate single-pointer checks
                if (point->isRangeCheck()) 
                    continue;
                bool erased = exclusionSet.erase(point->insertBefore);
                assert(erased);
                if (!::isPotentiallyReachable(funcStart, point->insertBefore, exclusionSet, &DT, &LI)) {
                    // point is not reachable, delete it
                    pointToUses.erase(point);
                    change = true;
                }
                exclusionSet.insert(point->insertBefore);
            }
        }
    }

    return change;
}