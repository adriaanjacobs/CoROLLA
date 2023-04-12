#pragma once

/*
    Code adapted from LLVM's CFG.cpp.
    Modified to remove BB limit & compute instruction-level reachability
*/

#include <llvm/IR/BasicBlock.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/IR/Dominators.h>
#include <optional>

// LoopInfo contains a mapping from basic block to the innermost loop. Find
// the outermost loop in the loop nest that contains BB.
inline const llvm::Loop *getOutermostLoop(const llvm::LoopInfo *LI, const llvm::BasicBlock *BB) {
  const llvm::Loop *L = LI->getLoopFor(BB);
  return L ? L->getOutermostLoop() : nullptr;
}

inline bool isPotentiallyReachableFromMany(
    llvm::SmallVectorImpl<llvm::BasicBlock *> &Worklist, const llvm::BasicBlock *StopBB,
    const llvm::SmallPtrSetImpl<llvm::BasicBlock *> *ExclusionSet, const llvm::DominatorTree *DT,
    const llvm::LoopInfo *LI) {
  // When the stop block is unreachable, it's dominated from everywhere,
  // regardless of whether there's a path between the two blocks.
  if (DT && !DT->isReachableFromEntry(StopBB))
    DT = nullptr;
 
  // We can't skip directly from a block that dominates the stop block if the
  // exclusion block is potentially in between.
  if (ExclusionSet && !ExclusionSet->empty())
    DT = nullptr;
 
  // Normally any block in a loop is reachable from any other block in a loop,
  // however excluded blocks might partition the body of a loop to make that
  // untrue.
  llvm::SmallPtrSet<const llvm::Loop *, 8> LoopsWithHoles;
  if (LI && ExclusionSet) {
    for (auto *BB : *ExclusionSet) {
      if (const llvm::Loop *L = getOutermostLoop(LI, BB))
        LoopsWithHoles.insert(L);
    }
  }
 
  const llvm::Loop *StopLoop = LI ? getOutermostLoop(LI, StopBB) : nullptr;
 
  llvm::SmallPtrSet<const llvm::BasicBlock*, 32> Visited;
  do {
    llvm::BasicBlock *BB = Worklist.pop_back_val();
    if (!Visited.insert(BB).second)
      continue;
    if (BB == StopBB)
      return true;
    if (ExclusionSet && ExclusionSet->count(BB))
      continue;
    if (DT && DT->dominates(BB, StopBB))
      return true;
 
    const llvm::Loop *Outer = nullptr;
    if (LI) {
      Outer = getOutermostLoop(LI, BB);
      // If we're in a loop with a hole, not all blocks in the loop are
      // reachable from all other blocks. That implies we can't simply jump to
      // the loop's exit blocks, as that exit might need to pass through an
      // excluded block. Clear Outer so we process BB's successors.
      if (LoopsWithHoles.count(Outer))
        Outer = nullptr;
      if (StopLoop && Outer == StopLoop)
        return true;
    }
 
    if (Outer) {
      // All blocks in a single loop are reachable from all other blocks. From
      // any of these blocks, we can skip directly to the exits of the loop,
      // ignoring any other blocks inside the loop body.
      Outer->getExitBlocks(Worklist);
    } else {
      Worklist.append(succ_begin(BB), succ_end(BB));
    }
  } while (!Worklist.empty());
 
  // We have exhausted all possible paths and are certain that 'To' can not be
  // reached from 'From'.
  return false;
}

inline bool isPotentiallyReachable(llvm::Instruction* from, llvm::Instruction* to, 
                                const llvm::DenseMap<llvm::BasicBlock*, llvm::DenseSet<llvm::Instruction*>>& exclusionMap, 
                                llvm::DominatorTree* domTree, llvm::LoopInfo* loopInfo
) {
    auto exclusionSetContains = [&] (llvm::Instruction* inst) {
        if (auto entry = exclusionMap.find(inst->getParent()); entry != exclusionMap.end())
            return entry->getSecond().contains(inst);
        return false;
    };

    // input sanitization to catch some probably unwanted behaviour
    assert(!exclusionSetContains(from));
    assert(!exclusionSetContains(to));
    assert(from->getFunction() == to->getFunction());

    // first the easy case: are any of the next instructions within the block in the exclusionSet or the target instruction?
    auto forwardIntraBlockReachable = [&] () -> std::optional<bool> {
        auto current = from;
        while ((current = current->getNextNode()) != nullptr) {
            if (current == to)
                return true;
            if (exclusionSetContains(current))
                return false;
        }
        return std::nullopt;
    } ();

    if (from->getParent() == to->getParent()) 
        if (from->comesBefore(to)) 
            assert(forwardIntraBlockReachable.has_value());

    if (forwardIntraBlockReachable.has_value()) 
        return forwardIntraBlockReachable.value();

    // now consider the case where `to` comes before `from`
    // as long as there's no excluders between the start of the block & `to`
    // it's safe to exclude the block from the exclusionSet
    auto reachableFromBlockEntry = [&] () -> std::optional<bool> {
        auto current = to;
        while ((current = current->getPrevNode()) != nullptr) {
            if (exclusionSetContains(current))
                return false; // inhibited
            assert(current != from); // we already checked this
        }
        return std::nullopt;
    } ();
    if (reachableFromBlockEntry.has_value()) {
        assert(reachableFromBlockEntry.value() == false);
        return reachableFromBlockEntry.value();
    }

    // `to` and `from` may still be in the same block, and `to` may still be reachable from `from`
    //      e.g. when `to` comes before `from` and is reachable from block entry, 
    //      or `to` and `from` are the same instruction
    if (from->getParent() == to->getParent())
        assert(to->comesBefore(from) || to == from);
    // the reachability question now reduces to: is the to&from block reachable from itself?
    // to answer this query, the to&from block should not be in the exclusionSet.

    // if `to` and `from` are in different blocks
    //  `to` definitely reaches its terminator
    //  and `from`  is definitely reachable from its block entry
    // so we can safely remove both `to` and `from` blocks from the exclusionSet
    
    llvm::SmallPtrSet<llvm::BasicBlock*, 32> blockExclusionSet;
    for (auto& [block, insts] : exclusionMap)
        if (!insts.empty())
            blockExclusionSet.insert(block);
    blockExclusionSet.erase(to->getParent());
    blockExclusionSet.erase(from->getParent());

    llvm::SmallVector<llvm::BasicBlock*> workList;
    workList.append(llvm::succ_begin(from->getParent()), llvm::succ_end(from->getParent()));

    bool isReachable = !workList.empty() && ::isPotentiallyReachableFromMany(workList, to->getParent(), &blockExclusionSet, domTree, loopInfo);
    return isReachable;
}

inline bool isPotentiallyReachable(llvm::Instruction* from, llvm::Instruction* to, 
                                const llvm::DenseSet<llvm::Instruction*>& exclusionSet, 
                                llvm::DominatorTree* domTree, llvm::LoopInfo* loopInfo
) {
    llvm::DenseMap<llvm::BasicBlock*, llvm::DenseSet<llvm::Instruction*>> exclusionMap;
    for (auto excl : exclusionSet)
        exclusionMap[excl->getParent()].insert(excl);
    
    return isPotentiallyReachable(from, to, exclusionMap, domTree, loopInfo);
}
