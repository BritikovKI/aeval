#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"

#include "seahorn/Analysis/DSA/Graph.hh"
#include "seahorn/Analysis/DSA/Global.hh"
#include "seahorn/Analysis/DSA/Local.hh"
#include "seahorn/Analysis/DSA/Cloner.hh"
#include "seahorn/Analysis/DSA/BottomUp.hh"
#include "seahorn/Analysis/DSA/CallSite.hh"
#include "seahorn/Analysis/DSA/CallGraph.hh"

#include "ufo/Stats.hh"

#include "avy/AvyDebug.h"

#include "boost/range/iterator_range.hpp"

static llvm::cl::opt<bool>
normalizeUniqueScalars("horn-sea-dsa-norm-unique-scalar",
            llvm::cl::desc("DSA: all callees and callers agree on unique scalars"),
            llvm::cl::init (true));

using namespace llvm;


/// CONTEXT-INSENSITIVE DSA 
namespace seahorn
{
  namespace dsa
  {

    void ContextInsensitiveGlobalAnalysis::
    resolveArguments (DsaCallSite &cs, Graph& g)
    {
      // unify return
      const Function &callee = *cs.getCallee ();
      if (g.hasRetCell(callee))
      {
        Cell &nc = g.mkCell(*cs.getInstruction(), Cell());
        const Cell& r = g.getRetCell(callee);
        Cell c (*r.getNode (), r.getOffset ());
        nc.unify(c);
      }

      // unify actuals and formals
      DsaCallSite::const_actual_iterator AI = cs.actual_begin(), AE = cs.actual_end();
      for (DsaCallSite::const_formal_iterator FI = cs.formal_begin(), FE = cs.formal_end();
           FI != FE && AI != AE; ++FI, ++AI) 
      {
        const Value *arg = (*AI).get();
        const Value *farg = &*FI;
        if (g.hasCell(*farg)) {
          Cell &c = g.mkCell(*arg, Cell());
          Cell &d = g.mkCell (*farg, Cell ());
          c.unify (d);
        }
      }
    }                                      

    bool ContextInsensitiveGlobalAnalysis::runOnModule (Module &M)
    {

      LOG("dsa-global", 
          errs () << "Started context-insensitive global analysis ... \n");

      ufo::Stats::resume ("CI-DsaAnalysis");

      m_graph.reset (new Graph (m_dl, m_setFactory));

      LocalAnalysis la (m_dl, m_tli);

      // -- bottom-up inlining of all graphs
      for (auto it = scc_begin (&m_cg); !it.isAtEnd (); ++it)
      {
        auto &scc = *it;

        // --- all scc members share the same local graph
        for (CallGraphNode *cgn : scc) 
        {
          Function *fn = cgn->getFunction ();
          if (!fn || fn->isDeclaration () || fn->empty ()) continue;
          
          // compute local graph
          Graph fGraph (m_dl, m_setFactory);
          la.runOnFunction (*fn, fGraph);

          m_fns.insert (fn);
          m_graph->import(fGraph, true);
        }

        // --- resolve callsites
        for (CallGraphNode *cgn : scc)
        {
          Function *fn = cgn->getFunction ();
          
          // XXX probably not needed since if the function is external
          // XXX it will have no call records
          if (!fn || fn->isDeclaration () || fn->empty ()) continue;
          
          // -- iterate over all call instructions of the current function fn
          // -- they are indexed in the CallGraphNode data structure
          for (auto &CallRecord : *cgn) 
          {
            ImmutableCallSite cs (CallRecord.first);
            DsaCallSite dsa_cs (cs);
            const Function *callee = dsa_cs.getCallee();
            // XXX We want to resolve external calls as well.
            // XXX By not resolving them, we pretend that they have no
            // XXX side-effects. This should be an option, not the only behavior
            if (callee && !callee->isDeclaration () && !callee->empty ())
            {
              assert (fn == dsa_cs.getCaller ());
              resolveArguments (dsa_cs, *m_graph);
            }
          }
        }
        m_graph->compress();
      }

      ufo::Stats::stop ("CI-DsaAnalysis");
      LOG("dsa-global", 
          errs () << "Finished context-insensitive global analysis.\n");

      return false;
    }


    const Graph& ContextInsensitiveGlobalAnalysis::getGraph(const Function&) const
    { assert(m_graph); return *m_graph; }

    Graph& ContextInsensitiveGlobalAnalysis::getGraph(const Function&)
    { assert(m_graph); return *m_graph; }

    bool ContextInsensitiveGlobalAnalysis::hasGraph(const Function&fn) const 
    { return m_fns.count(&fn) > 0; }

      
    /// LLVM pass

    ContextInsensitiveGlobal::ContextInsensitiveGlobal () 
        : DsaGlobalPass (ID), m_ga (nullptr) {}
          
    void ContextInsensitiveGlobal::getAnalysisUsage (AnalysisUsage &AU) const 
    {
      AU.addRequired<DataLayoutPass> ();
      AU.addRequired<TargetLibraryInfo> ();
      AU.addRequired<CallGraphWrapperPass> ();
      AU.setPreservesAll ();
    }
        
    bool ContextInsensitiveGlobal::runOnModule (Module &M)
    {
      auto &dl = getAnalysis<DataLayoutPass>().getDataLayout ();
      auto &tli = getAnalysis<TargetLibraryInfo> ();
      auto &cg = getAnalysis<CallGraphWrapperPass> ().getCallGraph ();

      m_ga.reset (new ContextInsensitiveGlobalAnalysis (dl, tli, cg, m_setFactory));
      return m_ga->runOnModule (M);
    }
  
  } // end namespace dsa
} // end namespace seahorn


/// CONTEXT-SENSITIVE DSA 
namespace seahorn
{
  namespace dsa 
  {

    // Clone caller nodes into callee and resolve arguments
    // XXX: this code is pretty much symmetric to the one defined in
    // BottomUp. They should be merged at some point.
    void ContextSensitiveGlobalAnalysis::
    cloneAndResolveArguments (const DsaCallSite &cs, 
                              Graph& callerG, Graph& calleeG)
    {      
      Cloner C (calleeG);
      
      // clone and unify globals 
      for (auto &kv : boost::make_iterator_range (callerG.globals_begin (),
                                                  callerG.globals_end ()))
      {
        Node &n = C.clone (*kv.second->getNode ());
        Cell c (n, kv.second->getOffset ());
        Cell &nc = calleeG.mkCell (*kv.first, Cell ());
        nc.unify (c);
      }

      // clone and unify return
      const Function &callee = *cs.getCallee ();
      if (calleeG.hasRetCell (callee) && callerG.hasCell (*cs.getInstruction ()))
      {
        Node &n = C.clone (*callerG.getCell (*cs.getInstruction ()).getNode());
        Cell c (n, callerG.getCell (*cs.getInstruction()).getOffset ());
        Cell &nc = calleeG.getRetCell (callee);
        nc.unify (c);
      }

      // clone and unify actuals and formals
      DsaCallSite::const_actual_iterator AI = cs.actual_begin(), AE = cs.actual_end();
      for (DsaCallSite::const_formal_iterator FI = cs.formal_begin(), FE = cs.formal_end();
           FI != FE && AI != AE; ++FI, ++AI) 
      {
        const Value *arg = (*AI).get();
        const Value *fml = &*FI;
        if (callerG.hasCell (*arg) && calleeG.hasCell (*fml))
        {
          Node &n = C.clone (*callerG.getCell (*arg).getNode ());
          Cell c (n, callerG.getCell (*arg).getOffset ());
          Cell &nc = calleeG.mkCell (*fml, Cell ());
          nc.unify (c);
        }
      }
      calleeG.compress();
    }

    // Decide which kind of propagation (if any) is needed
    ContextSensitiveGlobalAnalysis::PropagationKind 
    ContextSensitiveGlobalAnalysis::decidePropagation 
    (const DsaCallSite& cs, Graph &calleeG, Graph& callerG) 
    {
      PropagationKind res = UP;
      SimulationMapper sm;
      if (Graph::computeCalleeCallerMapping(cs, calleeG, callerG, 
                                            true,  /*only modified nodes*/
                                            false, /*no report if sanity check failed*/
                                            sm)) {
        if (sm.isFunction ())
          res = (sm.isInjective () ? NONE: DOWN);
      }

      return res;
    }

    template<typename WorkList>
    static void Insert (WorkList &w, const Instruction* CI)
    { // XXX: this is a very inefficient way of breaking cycles
      if (std::find(w.begin(), w.end(), CI) == w.end())
        w.push_back (CI);
    }

    template<typename Iter, typename WorkList>
    static void Insert (WorkList &w, Iter it, Iter et)
    { for (; it!=et;++it) Insert (w, *it); }

    void ContextSensitiveGlobalAnalysis::
    propagateTopDown (const DsaCallSite& cs, Graph &callerG, Graph& calleeG) 
    {
      cloneAndResolveArguments (cs, callerG, calleeG);

      LOG("dsa-global",
          if (decidePropagation (cs, calleeG, callerG) == DOWN)
          {
            errs () << "Sanity check failed:"
                    << " we should not need more top-down propagation\n";
          });
            
      assert (decidePropagation (cs, calleeG, callerG) != DOWN);
    }

    void ContextSensitiveGlobalAnalysis::
    propagateBottomUp (const DsaCallSite& cs, Graph &calleeG, Graph& callerG) 
    {
      BottomUpAnalysis::cloneAndResolveArguments (cs, calleeG, callerG);
      
      LOG("dsa-global",
          if (decidePropagation (cs, calleeG, callerG) == UP)
          {
            errs () << "Sanity check failed:"
                    << " we should not need more bottom-up propagation\n";
          });
      
      assert (decidePropagation (cs, calleeG, callerG) != UP);
    }


    bool ContextSensitiveGlobalAnalysis::runOnModule (Module &M) 
    {

      LOG("dsa-global", errs () << "Started context-sensitive global analysis ... \n");

      ufo::Stats::resume ("CS-DsaAnalysis");

      for (auto &F: M)
      { 
        if (F.isDeclaration() || F.empty())
          continue;
        
        GraphRef fGraph = std::make_shared<Graph> (m_dl, m_setFactory);
        m_graphs[&F] = fGraph;
      }

      // -- Run bottom up analysis on the whole call graph 
      //    and initialize worklist
      BottomUpAnalysis bu (m_dl, m_tli, m_cg);
      bu.runOnModule (M, m_graphs);

      DsaCallGraph dsaCG (m_cg);
      dsaCG.buildDependencies ();

      /// push in the worklist callsites for which two different
      /// callee nodes are mapped to the same caller node
      Worklist worklist;
      for (auto &kv: boost::make_iterator_range (bu.callee_caller_mapping_begin (),
                                                 bu.callee_caller_mapping_end ()))
      {
        auto const &simMapper = *(kv.second);
        if (!simMapper.isInjective ()) 
          worklist.push_back (kv.first);  // they do need top-down
      }

      /// -- top-down/bottom-up propagation until no change

      unsigned td_props = 0;
      unsigned bu_props = 0;
      while (!worklist.empty()) 
      {
        const Instruction* I = I = worklist.back();
        worklist.pop_back();

        if (const CallInst *CI = dyn_cast<CallInst> (I))
          if (CI->isInlineAsm())
            continue;

        ImmutableCallSite CS (I);
        DsaCallSite dsaCS (CS);

        auto callee = dsaCS.getCallee();
        if (!callee || callee->isDeclaration() || callee->empty())
          continue;

        assert (m_graphs.count (dsaCS.getCaller ()) > 0);
        assert (m_graphs.count (dsaCS.getCallee ()) > 0);
        
        Graph &callerG = *(m_graphs.find (dsaCS.getCaller())->second);
        Graph &calleeG = *(m_graphs.find (dsaCS.getCallee())->second);

        // -- find out which propagation is needed if any
        auto propKind = decidePropagation  (dsaCS, calleeG, callerG);
        if (propKind == DOWN)
        {
          propagateTopDown (dsaCS, callerG, calleeG); 
          td_props++;
          auto &calleeU = dsaCG.getUses (*callee);
          auto &calleeD = dsaCG.getDefs (*callee);
          Insert(worklist, calleeU.begin (), calleeU.end ()); // they might need bottom-up
          Insert(worklist, calleeD.begin (), calleeD.end ()); // they might need top-down
        }
        else if (propKind == UP)
        {
          propagateBottomUp (dsaCS, calleeG, callerG);
          bu_props++;
          auto &callerU = dsaCG.getUses (*dsaCS.getCaller());
          auto &callerD = dsaCG.getDefs (*dsaCS.getCaller());
          Insert (worklist, callerU.begin (), callerU.end ());  // they might need bottom-up
          Insert (worklist, callerD.begin (), callerD.end ());  // they might need top-down
        }
      }

      LOG("dsa-global", 
          errs () << "-- Number of top-down propagations=" << td_props << "\n";
          errs () << "-- Number of bottom-up propagations=" << bu_props << "\n";);

      LOG("dsa-global", checkNoMorePropagation ());

      assert (checkNoMorePropagation ());

      if (normalizeUniqueScalars)
      {
        UniqueScalarAnalysis<ContextSensitiveGlobalAnalysis> usa (*this, dsaCG);
        usa.runOnModule (M);
      }

      LOG("dsa-global", errs () << "Finished context-sensitive global analysis\n");

      ufo::Stats::stop ("CS-DsaAnalysis");          

      return false;
    }

    // Perform some sanity checks:
    // 1) each callee node can be simulated by its corresponding caller node.
    // 2) no two callee nodes are mapped to the same caller node.
    bool ContextSensitiveGlobalAnalysis::checkNoMorePropagation() 
    {
      for (auto it = scc_begin (&m_cg); !it.isAtEnd (); ++it)
      {
        auto &scc = *it;
        for (CallGraphNode *cgn : scc)
        {
          Function *fn = cgn->getFunction ();
          if (!fn || fn->isDeclaration () || fn->empty ()) continue;
          
          for (auto &callRecord : *cgn)
          {
            ImmutableCallSite CS (callRecord.first);
            DsaCallSite cs (CS);

            const Function *callee = cs.getCallee ();
            if (!callee || callee->isDeclaration () || callee->empty ()) continue;

            assert (m_graphs.count (cs.getCaller ()) > 0);
            assert (m_graphs.count (cs.getCallee ()) > 0);
        
            Graph &callerG = *(m_graphs.find (cs.getCaller())->second);
            Graph &calleeG = *(m_graphs.find (cs.getCallee())->second);
            PropagationKind pkind = decidePropagation (cs, calleeG, callerG);
            if (pkind != NONE)
            {
              auto pkind_str = (pkind==UP)? "bottom-up": "top-down";
              errs () << "WARNING sanity check failed:" 
                      << *(cs.getInstruction ()) << " requires " 
                      << pkind_str << " propagation.\n";
              return false;
            }
          }
        }
      }
      errs () << "Sanity check succeed: global propagation completed!\n";
      return true;
    }

    const Graph &ContextSensitiveGlobalAnalysis::getGraph (const Function &fn) const
    { return *(m_graphs.find (&fn)->second); }

    Graph &ContextSensitiveGlobalAnalysis::getGraph (const Function &fn)
    { return *(m_graphs.find (&fn)->second); }

    bool ContextSensitiveGlobalAnalysis::hasGraph (const Function &fn) const
    { return m_graphs.count (&fn) > 0; }

    /// LLVM pass

    ContextSensitiveGlobal::ContextSensitiveGlobal () 
        : DsaGlobalPass (ID), m_ga (nullptr) {}
          
    void ContextSensitiveGlobal::getAnalysisUsage (AnalysisUsage &AU) const 
    {
      AU.addRequired<DataLayoutPass> ();
      AU.addRequired<TargetLibraryInfo> ();
      AU.addRequired<CallGraphWrapperPass> ();
      AU.setPreservesAll ();
    }

    bool ContextSensitiveGlobal::runOnModule (Module &M)
    {
      auto &dl = getAnalysis<DataLayoutPass>().getDataLayout ();
      auto &tli = getAnalysis<TargetLibraryInfo> ();
      auto &cg = getAnalysis<CallGraphWrapperPass> ().getCallGraph ();

      m_ga.reset (new ContextSensitiveGlobalAnalysis (dl, tli, cg, m_setFactory));
      return m_ga->runOnModule (M);
    }

  }
}

namespace seahorn
{
  namespace dsa
  {

    template<class GA>
    void UniqueScalarAnalysis<GA>::join (const DsaCallSite &cs, 
                                         Node &calleeN, Node &callerN, 
                                         std::vector<const Instruction*> &w)
    {

      if (calleeN.getUniqueScalar () && callerN.getUniqueScalar ())
      { 
        assert (calleeN.getUniqueScalar () == callerN.getUniqueScalar ()); 
      }
      else if (calleeN.getUniqueScalar ()) 
      {
        calleeN.setUniqueScalar (nullptr);

        if (const Function *fn = cs.getCallee ())
        {
          for (auto cs: m_dsaCG.getUses (*fn)) Insert(w, cs); 
          for (auto cs: m_dsaCG.getDefs (*fn)) Insert(w, cs); 
        }
        
        LOG("dsa-unique-scalar",
            errs () << "callee node " << calleeN << " becomes a non-unique scalar\n";);
      }
      else if (callerN.getUniqueScalar ()) 
      {
        callerN.setUniqueScalar (nullptr);
        
        if (const Function *fn = cs.getCaller ())
        {
          for (auto cs: m_dsaCG.getUses (*fn)) Insert(w, cs); 
          for (auto cs: m_dsaCG.getDefs (*fn)) Insert(w, cs); 
        }
        
        LOG("dsa-unique-scalar",
            errs () << "caller node " << callerN << " becomes a non-unique scalar\n";);
      }
    }
    
    template<class GA>
    void UniqueScalarAnalysis<GA>::normalize (const DsaCallSite &cs, 
                                              Graph& calleeG, Graph& callerG,
                                              std::vector<const Instruction*> &w)
    {
      // globals 
      for (auto &kv : boost::make_iterator_range (calleeG.globals_begin (),
                                                  calleeG.globals_end ()))
      {
        Cell &c = *kv.second;
        Cell &nc = callerG.mkCell (*kv.first, Cell ());
        join (cs, *c.getNode(), *nc.getNode(), w);
      }

      // return
      const Function &callee = *cs.getCallee ();
      if (calleeG.hasRetCell (callee) && callerG.hasCell (*cs.getInstruction ()))
      {
        Cell &c = calleeG.getRetCell (callee);
        Cell &nc = callerG.mkCell (*cs.getInstruction (), Cell ());
        join (cs, *c.getNode(), *nc.getNode(), w);
      }

      // actuals and formals
      DsaCallSite::const_actual_iterator AI = cs.actual_begin(), AE = cs.actual_end();
      for (DsaCallSite::const_formal_iterator FI = cs.formal_begin(), FE = cs.formal_end();
           FI != FE && AI != AE; ++FI, ++AI) 
      {
        const Value *arg = (*AI).get();
        const Value *fml = &*FI;
        if (callerG.hasCell (*arg) && calleeG.hasCell (*fml))
        {
          Cell &c = calleeG.mkCell (*fml, Cell ());
          Cell &nc =  callerG.mkCell (*arg, Cell ());
          join (cs, *c.getNode(), *nc.getNode(), w);
        }
      }
    }
  
    template<class GA>
    bool UniqueScalarAnalysis<GA>::runOnModule(Module &M) 
    {
      std::vector<const Instruction*> W;

      for (auto it = scc_begin (&m_dsaCG.getCallGraph()); !it.isAtEnd (); ++it)
      {
        auto &scc = *it;
        for (CallGraphNode *cgn : scc)
        {
          Function *fn = cgn->getFunction ();
          if (!fn || fn->isDeclaration () || fn->empty ()) continue;
          
          for (auto &callRecord : *cgn)
          {
            ImmutableCallSite CS (callRecord.first);
            DsaCallSite dsaCS (CS);

            const Function *callee = dsaCS.getCallee ();
            if (!callee || callee->isDeclaration () || callee->empty ()) continue;

            if (m_ga.hasGraph (*dsaCS.getCaller()) && m_ga.hasGraph (*dsaCS.getCallee()))
            {
              Graph &calleeG = m_ga.getGraph (*dsaCS.getCallee());        
              Graph &callerG = m_ga.getGraph (*dsaCS.getCaller());
              normalize (dsaCS, calleeG, callerG, W);
            }
          }
        }
      }

      while (!W.empty()) 
      {
        const Instruction* I = W.back ();
        ImmutableCallSite CS (I);
        DsaCallSite dsaCS (CS);
        W.pop_back ();

        assert (dsaCS.getCaller ());
        assert (dsaCS.getCallee ());

        if (m_ga.hasGraph (*dsaCS.getCaller ()) && m_ga.hasGraph (*dsaCS.getCallee ()))
        {
          Graph &calleeG = m_ga.getGraph (*dsaCS.getCallee());        
          Graph &callerG = m_ga.getGraph (*dsaCS.getCaller());
          normalize (dsaCS, calleeG, callerG, W);
        }
      }
      
      return false;
    }
  }
}

char seahorn::dsa::ContextInsensitiveGlobal::ID = 0;

char seahorn::dsa::ContextSensitiveGlobal::ID = 0;

static llvm::RegisterPass<seahorn::dsa::ContextInsensitiveGlobal> 
X ("sea-dsa-ci-global", "Context-insensitive Dsa analysis");

static llvm::RegisterPass<seahorn::dsa::ContextSensitiveGlobal> 
Y ("sea-dsa-cs-global", "Context-sensitive Dsa analysis");

