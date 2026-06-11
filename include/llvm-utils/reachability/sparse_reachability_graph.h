#pragma once

#include <corolla/util.h>
#include <corolla/reachability/cfg_reachability.h>

struct ReachabilityGraph {
    llvm::DenseMap<llvm::Instruction*, llvm::DenseSet<llvm::Instruction*>> instToSuccs;
    llvm::DenseMap<llvm::Instruction*, llvm::DenseSet<llvm::Instruction*>> instToPreds;

    // build the graph of insts to their direct successing and predecessing insts
    ReachabilityGraph(const llvm::DenseSet<llvm::Instruction*>& insts, llvm::DominatorTree* domTree, llvm::LoopInfo* loopInfo) {
        llvm::DenseMap<llvm::BasicBlock*, llvm::DenseSet<llvm::Instruction*>> exclusionMap;
        for (auto inst : insts)
            exclusionMap[inst->getParent()].insert(inst);

        auto eraseFromExclusionSet = [&] (llvm::Instruction* inst) -> std::tuple<decltype(exclusionMap)::iterator, bool> {
            auto blockIt = exclusionMap.find(inst->getParent());
            assert(blockIt != exclusionMap.end());
            return {blockIt, blockIt->getSecond().erase(inst)};
        };
        
        for (auto req : insts) {
            auto [reqBlockIt, dbg_erased] = eraseFromExclusionSet(req);
            assert(dbg_erased);
            for (auto potSucc : insts) {
                auto [potSuccBlockIt, erased] = eraseFromExclusionSet(potSucc);
                if (isPotentiallyReachable(req, potSucc, exclusionMap, domTree, loopInfo)) 
                    instToSuccs[req].insert(potSucc);
                if (erased) // if req == potSucc, it shouldnt be reintroduced here
                    potSuccBlockIt->getSecond().insert(potSucc);
            }
            reqBlockIt->getSecond().insert(req);
        }

        // reverse map
        for (auto& [req, succs] : instToSuccs) {
            for (auto succ : succs) {
                instToPreds[succ].insert(req);
            }
        }
    }
};

