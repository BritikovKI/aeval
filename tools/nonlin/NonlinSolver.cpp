#include "deep/NonlinCHCsolver.hpp"

using namespace ufo;
using namespace std;

bool getBoolValue(const char * opt, bool defValue, int argc, char ** argv)
{
    for (int i = 1; i < argc; i++)
    {
        if (strcmp(argv[i], opt) == 0) return true;
    }
    return defValue;
}

char * getStrValue(const char * opt, char * defValue, int argc, char ** argv)
{
    for (int i = 1; i < argc-1; i++)
    {
        if (strcmp(argv[i], opt) == 0)
        {
            return argv[i+1];
        }
    }
    return defValue;
}

int getIntValue(const char * opt, int defValue, int argc, char ** argv)
{
    for (int i = 1; i < argc-1; i++)
    {
        if (strcmp(argv[i], opt) == 0)
        {
            char* p;
            int num = strtol(argv[i+1], &p, 10);
            if (*p) return 1;      // if used w/o arg, return boolean
            else return num;
        }
    }
    return defValue;
}
void getStrValues(const char * opt, vector<string> & values, int argc, char ** argv)
{
    for (int i = 1; i < argc-1; i++)
    {
        if (strcmp(argv[i], opt) == 0)
        {
            values.push_back(string(argv[i+1]));
        }
    }
}

static inline void splitLine(vector<string>& input, string input_str, char d){
  if (input_str.empty()) return;
  string s = input_str;
  size_t pos = 0;
  std::string token;
  while ((pos = s.find(d)) != std::string::npos) {
    token = s.substr(0, pos);
    input.push_back(token);
    s.erase(0, pos + 1);
  }
  input.push_back(s);
}

bool isContract(string w1){
  string contract_string = "contract";
  return w1.find(contract_string) != std::string::npos;
}

void print_signature(map<string, map<string, vector<string>>>& signature){
  for (auto const &pair: signature) {
    outs() << "contract:" << pair.first << "\n";
    for(auto f: pair.second){
      outs() << "{" << f.first << ": ";
      for(auto p: f.second){
        outs() << p << " ";
      }
      outs() << "}\n";
    }
  }
}


static inline void getSignature(map<string, map<string, vector<string>>>& signature, string str)
{
    vector<string> tmp_split;
    splitLine(tmp_split, str, '^');
    map<string, vector<string>> current;
    string current_contract_name;

    for (auto i: tmp_split){
      if (isContract(i)){
        if (!current.empty()){
          signature.insert({current_contract_name, current});
        }
        map<string, vector<string>> new_current;
        current = new_current;
        vector<string> tmp;
        splitLine(tmp, i, ':');
        vector<string> tmp_f;
        splitLine(tmp_f, tmp[1], ',');
        vector<string> tmp_name;
        splitLine(tmp_name, tmp[0], '_');
        current.insert({tmp[0], tmp_f});
        current_contract_name = tmp_name[1];
      }else{
        vector<string> tmp;
        splitLine(tmp, i, ':');
        vector<string> tmp_f;
        splitLine(tmp_f, tmp[1], ',');
        current.insert({tmp[0], tmp_f});
      }
    }

    if (!current.empty()){
      signature.insert({current_contract_name, current});
    }

    //print_signature(signature);
}


const char *OPT_HELP = "--help";
const char *OPT_MAX_ATTEMPTS = "--attempts";
const char *OPT_TO = "--to";
const char *OPT_LB = "--lb";
const char *OPT_LMAX = "--max";
const char *OPT_ELIM = "--skip-elim";
const char *OPT_ARITHM = "--skip-arithm";
const char *OPT_SEED = "--inv-mode";
const char *OPT_GET_FREQS = "--freqs";
const char *OPT_ADD_EPSILON = "--eps";
const char *OPT_AGG_PRUNING = "--aggp";
const char *OPT_DATA_LEARNING = "--data";
const char *OPT_PROP = "--prop";
const char *OPT_DISJ = "--disj";
const char *OPT_D1 = "--all-mbp";
const char *OPT_D2 = "--phase-prop";
const char *OPT_D3 = "--phase-data";
const char *OPT_D4 = "--stren-mbp";
const char *OPT_MBP = "--eqs-mbp";
const char *OPT_DEBUG = "--debug";

int main (int argc, char ** argv)
{
    map<string, map<string, vector<string>>> signature;
    getSignature(signature, getStrValue("--keys", NULL, argc, argv));
    bool to_skip = getBoolValue("--no-term", false, argc, argv);
    int lookahead = getIntValue("--lookahead", 3, argc, argv);
    bool prio = getBoolValue("--prio", false, argc, argv);
    bool lb = getBoolValue(OPT_LB, false, argc, argv);
    bool lmax = getBoolValue(OPT_LMAX, false, argc, argv);

    // All other attrs are inherited from FreqHorn:
    bool help = getBoolValue(OPT_HELP, false, argc, argv);
    int max_attempts = getIntValue(OPT_MAX_ATTEMPTS, 10, argc, argv);
    int to = getIntValue(OPT_TO, 1000, argc, argv);
    bool densecode = getBoolValue(OPT_GET_FREQS, false, argc, argv);
    bool aggressivepruning = getBoolValue(OPT_AGG_PRUNING, false, argc, argv);
    bool do_elim = !getBoolValue(OPT_ELIM, false, argc, argv);
    bool do_arithm = !getBoolValue(OPT_ARITHM, false, argc, argv);
    int invMode = getIntValue(OPT_SEED, 0, argc, argv);
    int do_prop = getIntValue(OPT_PROP, 0, argc, argv);
    int do_disj = getBoolValue(OPT_DISJ, false, argc, argv);
    bool do_dl = getBoolValue(OPT_DATA_LEARNING, false, argc, argv);
    int mbp_eqs = getIntValue(OPT_MBP, 0, argc, argv);
    bool d_m = getBoolValue(OPT_D1, false, argc, argv);
    bool d_p = getBoolValue(OPT_D2, false, argc, argv);
    bool d_d = getBoolValue(OPT_D3, false, argc, argv);
    bool d_s = getBoolValue(OPT_D4, false, argc, argv);
    int debug = getIntValue(OPT_DEBUG, 0, argc, argv);

    if (help) {
      // TODO: write help message
    }

    if (do_disj && (!d_p && !d_d))
    {
        errs() << "WARNING: either \"" << OPT_D2 << "\" or \"" << OPT_D3 << "\" should be enabled\n"
               << "enabling \"" << OPT_D3 << "\"\n";
        d_d = true;
    }

    if (d_m || d_p || d_d || d_s) do_disj = true;
    if (do_disj) do_dl = true;

    testgen(argv[argc-1], signature, max_attempts, to, densecode, aggressivepruning,
            do_dl, do_elim, do_disj, do_prop, d_m, d_p, d_d, d_s,
            to_skip, invMode, lookahead, lb, lmax, prio, debug);
    return 0;
}
