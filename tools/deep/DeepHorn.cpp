#include <boost/mpi/environment.hpp>
#include <boost/mpi/communicator.hpp>
#include <boost/serialization/vector.hpp>
#include <boost/serialization/shared_ptr.hpp>
#include "deep/RndLearner.hpp"
#include "deep/Distributed.hpp"
#include <chrono>
#include <thread>

using namespace ufo;
using namespace std;


class OpenCandidateSet {
private:
  RndLearner& rndLearner;
  const unsigned invCnt;
  vector<vector<LAdisj>> candidates;
  const bool aggressivepruning;

  void fillCandidateVector(vector<LAdisj>& v, unsigned wIdx) {

    assert(v.empty());

    for (size_t j = 0; j < invCnt; j++) {
      while (1) {
        LAfactory& lf = rndLearner.getLAFactory(j);
        boost::optional<LAdisj&> candDisj = lf.getFreshCandidateDisj();
        if (!candDisj)
          continue;  // retry

        Expr cand = lf.toExpr(*candDisj);
        if (rndLearner.isTautology(cand)) {  // keep searching
          lf.assignPrioritiesForLearnt(lf.samples.back());
          continue;  // retry
        }

        if (lf.nonlinVars.size() > 0 && !rndLearner.isSMTSat(cand)) {  // keep searching
          lf.assignPrioritiesForFailed(lf.samples.back());
          continue;  // retry
        }

        if (aggressivepruning && candidateInWorkerRange(*candDisj, 0, wIdx))
          continue;

        v.push_back(*candDisj);
        break;
      }
    }

    assert(v.size() == invCnt);
  }

  bool candidateInWorkerRange(LAdisj& cand, unsigned a, unsigned e) {
    // This is a naive implementation, but, in practice, very little time is
    // spent in this method.
    for (unsigned i = a; i < e; i++) {
      for (unsigned j = 0; j < invCnt; j++) {
        if (candidates[i][j].getId() == cand.getId())
          return true;
      }
    }
    return false;
  }

public:
  OpenCandidateSet(RndLearner& rl, unsigned wCnt, unsigned iCnt, bool a) :
    rndLearner(rl), invCnt(iCnt), candidates(), aggressivepruning(a)
  {
    // Prealloc memory
    candidates.reserve(wCnt);
    for (size_t i = 0; i < wCnt; i++) {
      vector<LAdisj>& inner = *candidates.emplace(candidates.cend());
      inner.reserve(invCnt);
    }
  }

  void clearCandidatesForWorker(unsigned wIdx) {
    candidates[wIdx].clear();
  }

  int fillCandidatesForEmptyWorker() {
    for (size_t i = 0; i < candidates.size(); i++) {
      if (candidates[i].empty()) {
        fillCandidateVector(candidates[i], i);
        return i;
      }
    }
    return -1;
  }

  vector<LAdisj>& operator[](const int idx) {
    return candidates[idx];
  }
};


int main (int argc, char **argv)
{
  std::srand(std::time(0));

  // Initialize MPI
  boost::mpi::environment env(argc, argv);
  boost::mpi::communicator world;
  if (world.size() == 1) {
    cerr << "worker cnt. 1 unsupported; would result in 1 master, 0 workers\n";
    return 2;
  }

  // Parse command-line arguments
  if (argc == 1) {
    cerr << "At least an input file should be given\n";
    return 1;
  }
  const int maxAttempts = argc > 2 ? atoi(argv[1]) : 2000000;
  const bool densecode = argc > 3 ? atoi(argv[2]) : true;
  const bool aggressivepruning = argc > 4 ? atoi(argv[3]) : true;

  // Initialize all the heavy machinery, incl. parsing theinput file
  ExprFactory m_efac;
  EZ3 z3(m_efac);

  CHCs ruleManager(m_efac, z3);
  ruleManager.parse(string(argv[argc-1]));

  RndLearner ds(m_efac, z3, ruleManager, densecode, aggressivepruning);
  ds.setupSafetySolver();

  const int invCnt = ruleManager.decls.size();
  if (invCnt > 1) {
    outs() << "WARNING: learning multiple invariants is currently unstable\n"
           << "         it is suggested to disable \'aggressivepruning\'\n";
  }

  for (auto& dcl: ruleManager.decls)
    ds.initializeDecl(dcl);

  if (world.rank() == 0) {
    //
    // Master node
    //
    OpenCandidateSet openCandidates(ds, world.size() - 1, ds.invNumber(), aggressivepruning);
    vector<vector<std::shared_ptr<WorkerResult>>> forwardResultOutbox(world.size() - 1);
    const auto start = std::chrono::steady_clock::now();

    bool success = false;
    unsigned attI = 0;
    while (!success && attI < maxAttempts) {
      // TODO: this can actually exceed maxAttempts; fix
      while (1) {
        // vector<boost::mpi::request> sends;

        // Any workers not doing anything at the moment? Generate some cands.
        auto fillResult = openCandidates.fillCandidatesForEmptyWorker();
        if (fillResult < 0) break;
        unsigned workerIdx = (unsigned)fillResult;

        // Send header msg.
        auto& workerOutbox = forwardResultOutbox[workerIdx];
        StartIterMsg startMsg { false, attI, workerOutbox.size() };
        // sends.push_back(world.isend(workerIdx + 1, MSG_TAG_NORMAL, startMsg));
        world.send(workerIdx + 1, MSG_TAG_NORMAL, startMsg);

        // Send any outstanding lemmas (async)
        for (auto it = workerOutbox.begin(); it != workerOutbox.end(); it++) {
          world.send(workerIdx + 1, MSG_TAG_NORMAL, *it);
          // sends.push_back(world.isend(workerIdx + 1, MSG_TAG_NORMAL, *it));
        }
        workerOutbox.clear();

        // Send the just-generated candidates (async)
        for (size_t j = 0; j < invCnt; j++) {
          auto c = openCandidates[workerIdx][j];
          world.send(workerIdx + 1, MSG_TAG_NORMAL, c);
          // sends.push_back(world.isend(workerIdx + 1, MSG_TAG_NORMAL, c));
        }
        attI++;

        // Join sends
        // boost::mpi::wait_all(sends.begin(), sends.end());
      }

      // Respond to results
      std::shared_ptr<WorkerResult> result;
      auto rMsgS = world.recv(boost::mpi::any_source, MSG_TAG_NORMAL, result);
      if (result->kind == WorkerResultKindDone) {
        openCandidates.clearCandidatesForWorker(rMsgS.source() - 1);
      } else if (result->kind == WorkerResultKindFoundInvariants) {
        success = true;
      } else {
        ds.integrateWorkerResult(*result);
        if (result->kind == WorkerResultKindLemma) {
          // assert(ds.checkSafety());
          for (size_t i = 0; i < world.size() - 1; i++) {
            if (i == rMsgS.source() - 1)
              continue;
            forwardResultOutbox[i].push_back(result);
          }
        }
      }
    }
    sendToOthers(world, MSG_TAG_NORMAL, (StartIterMsg){ true, attI, 0 });

    // Print results
    if (success) {
      auto end = std::chrono::steady_clock::now();
      auto elapsed = std::chrono::duration<double, std::milli>(end - start);
      stringstream elapsedStream;
      elapsedStream << fixed << setprecision(2) << elapsed.count()/1000.0;
      outs() << "\n -----> Success after " << attI << " iterations, \n";
      // outs() << "        total number of SMT checks: " << numOfSMTChecks << ",\n";
      outs() << "        elapsed: " << elapsedStream.str() << "s\n";
    } else {
      outs() << "\nNo success after " << maxAttempts << " iterations\n";
      // outs() << "        total number of SMT checks: " << numOfSMTChecks << "\n";
    }
  } else {
    //
    // Slave node
    //
    ds.workerMain(world);
  }

  return 0;
}
