#ifndef HORNNONLIN__HPP__
#define HORNNONLIN__HPP__

#include "ae/AeValSolver.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  // all adapted from Horn.hpp; experimental; to merge with Horn.hpp at some point
  inline bool rewriteHelperConsts_nonlinear(Expr& body, Expr v1, Expr v2)
  {
    if (isOpX<MPZ>(v1))
    {
      body = mk<AND>(body, mk<EQ>(v1, v2));
      return true;
    }
    else if (isOpX<TRUE>(v1))
    {
      body = mk<AND>(body, v2);
      return true;
    }
    else if (isOpX<FALSE>(v1))
    {
      body = mk<AND>(body, mk<NEG>(v2));
      return true;
    }
    return false;
  }

  struct HornRuleExt
  {
    vector<ExprVector> srcVars;
    ExprVector dstVars;
    ExprVector locVars;

    Expr body;
    Expr head;

    ExprVector srcRelations;
    Expr dstRelation;

    bool isFact;
    bool isQuery;
    bool isInductive;
    map<int, Expr> arg_names;

    void assignVarsAndRewrite (ExprVector& _srcVars, vector<ExprVector>& invVarsSrc,
                               ExprVector& _dstVars, ExprVector& invVarsDst)
    {
      int counter = 0;
      for (int i = 0; i < invVarsSrc.size(); i++)
      {
        ExprVector tmp;
        for (int j = 0; j < invVarsSrc[i].size(); j++)
        {
          tmp.push_back(invVarsSrc[i][j]);
          body = mk<AND>(body, mk<EQ>(_srcVars[counter], tmp[j]));
          counter++;;
        }
        srcVars.push_back(tmp);
      }

      for (int i = 0; i < _dstVars.size(); i++)
      {
        // primed copy of var:
        Expr new_name = mkTerm<string> (lexical_cast<string>(invVarsDst[i]) + "'", body->getFactory());
        Expr var = cloneVar(invVarsDst[i], new_name);
        dstVars.push_back(var);
        body = mk<AND>(body, mk<EQ>(_dstVars[i], dstVars[i]));
        arg_names[i] = _dstVars[i];
      }
    }
  };

  class CHCs
  {
    private:
    set<int> indeces;
    string varname = "_FH_";

    public:

    ExprFactory &m_efac;
    EZ3 &m_z3;

    ExprSet decls;
    Expr failDecl;
    ExprVector extras;
    vector<HornRuleExt> chcs;
    vector<vector<HornRuleExt>> functionBasedChcs;
    int index_fact_chc;
    vector<int> index_cycle_chc;
    map<Expr, ExprVector> invVars;
    map<Expr, vector<int>> incms;
    map<Expr, int> expr_id;
    int qCHCNum;  // index of the query in chc
    int total_var_cnt = 0;
    ExprVector constructors;
    string infile;

      //ToDo: Remove or recheck later on; move from Horn.hpp
    int debug;

    CHCs(ExprFactory &efac, EZ3 &z3) : m_efac(efac), m_z3(z3) {};

    bool isFapp (Expr e)
    {
      if (isOpX<FAPP>(e))
        if (e->arity() > 0)
          if (isOpX<FDECL>(e->arg(0)))
            if (e->arg(0)->arity() >= 2)
              return true;
      return false;
    }


    vector<HornRuleExt> getParents(HornRuleExt chc) {
      assert(std::find_if(chcs.begin(), chcs.end(), [chc](HornRuleExt comp) { return chc.body == comp.body; }) != chcs.end());
      if(chc.isFact) return {};
      auto parentsExpr = chc.srcRelations;
      printf("((((((((((((((((((\n");
      print(chc);
      printf("******************\n");
      vector<HornRuleExt> parents;
      for(HornRuleExt candidate: chcs){
        if(std::find(parentsExpr.begin(), parentsExpr.end(), candidate.dstRelation) != parentsExpr.end() &&
             candidate.dstRelation != chc.dstRelation){
          print(candidate);
          parents.push_back(candidate);
        }
      }
      printf("))))))))))))))))))\n");
      return parents;
    }

    HornRuleExt getChild(HornRuleExt const chc) {
      assert(std::find_if(chcs.begin(), chcs.end(), [chc](HornRuleExt comp) { return chc.body == comp.body; }) != chcs.end());
      auto parentsExpr = chc.dstRelation;
      HornRuleExt child = *std::find_if(chcs.begin(), chcs.end(),
                                          [parentsExpr](HornRuleExt elem){
        return (std::find(elem.srcRelations.begin(), elem.srcRelations.end(), parentsExpr) != elem.srcRelations.end());
      });

      return child;
    }

    void splitBody (HornRuleExt& hr, ExprVector& srcVars, ExprSet& lin)
    {
      getConj (hr.body, lin);
      for (auto c = lin.begin(); c != lin.end(); )
      {
        Expr cnj = *c;
        if (isOpX<FAPP>(cnj) && find(hr.locVars.begin(), hr.locVars.end(), cnj) == hr.locVars.end())
        {
          if(hr.body->arity() > 0) {
            assert(isOpX<FDECL>(cnj->left()));
            Expr rel = cnj->left();
            if (rel->arity() >= 2) {
              addDecl(rel);
              hr.srcRelations.push_back(rel->arg(0));
              for (auto it = cnj->args_begin() + 1; it != cnj->args_end(); ++it)
                srcVars.push_back(*it);
            }
            c = lin.erase(c);
          }
        }
        else ++c;
      }
    }

    void addDecl (Expr a)
    {
      if (invVars[a->arg(0)].empty())
      {
        decls.insert(a);
        for (int i = 1; i < a->arity()-1; i++)
        {
          Expr new_name = mkTerm<string> (varname + to_string(total_var_cnt), m_efac);
          total_var_cnt++;
          Expr arg = a->arg(i);
          if (!isOpX<INT_TY> (arg) && !isOpX<REAL_TY> (arg) && !isOpX<BOOL_TY> (arg) && !isOpX<ARRAY_TY> (arg) && !isOpX<AD_TY> (arg))
          {
            errs() << "Argument #" << i << " of " << a << " is not supported\n";
            exit(1);
          }
          Expr var;
          if (isOpX<INT_TY> (a->arg(i)))
              var = bind::intConst(new_name);
          else if (isOpX<REAL_TY> (a->arg(i)))
              var = bind::realConst(new_name);
          else if (isOpX<BOOL_TY> (a->arg(i)))
              var = bind::boolConst(new_name);
          else if (isOpX<ARRAY_TY> (a->arg(i)))
              var = bind::mkConst(new_name, mk<ARRAY_TY>(a->arg(i)->left(), a->arg(i)->right()));
          else if (isOpX<AD_TY>(a->arg(i))){
              ExprVector type;
              type.push_back(a->arg(i));
              var = bind::fapp(bind::fdecl (new_name, type));
          }
          else
              assert(0);
          invVars[a->arg(0)].push_back(var);
        }
      }
    }

    Expr normalize (Expr& r, HornRuleExt& hr)
    {
      r = regularizeQF(r);

      // TODO: support more syntactic replacements
      while (isOpX<FORALL>(r))
      {
        for (int i = 0; i < r->arity() - 1; i++)
        {
          hr.locVars.push_back(bind::fapp(r->arg(i)));
        }
        r = r->last();
      }

      if (isOpX<NEG>(r) && isOpX<EXISTS>(r->first()))
      {
        for (int i = 0; i < r->first()->arity() - 1; i++)
          hr.locVars.push_back(bind::fapp(r->first()->arg(i)));

        r = mk<IMPL>(r->first()->last(), mk<FALSE>(m_efac));
      }

      if (isOpX<NEG>(r))
      {
        r = mk<IMPL>(r->first(), mk<FALSE>(m_efac));
      }
      else if (isOpX<OR>(r) && r->arity() == 2 && isOpX<NEG>(r->left()) && hasUninterp(r->left()))
      {
        r = mk<IMPL>(r->left()->left(), r->right());
      }
      else if (isOpX<OR>(r) && r->arity() == 2 && isOpX<NEG>(r->right()) && hasUninterp(r->right()))
      {
        r = mk<IMPL>(r->right()->left(), r->left());
      }

      if (isOpX<IMPL>(r) && !isFapp(r->right()) && !isOpX<FALSE>(r->right()))
      {
        if (isOpX<TRUE>(r->right()))
        {
          return NULL;
        }
        r = mk<IMPL>(mk<AND>(r->left(), mk<NEG>(r->right())), mk<FALSE>(m_efac));
      }

      if (!isOpX<IMPL>(r)) r = mk<IMPL>(mk<TRUE>(m_efac), r);

      return r;
    }

    bool hasOnlyInduct(Expr rel, vector<int>& indexes)
    {
      int num = 0;
      for (int i = 0; i < chcs.size(); i++)
      {
        if (chcs[i].dstRelation == rel)
        {
          if (chcs[i].isFact)
          {
            indexes.clear();
            return false;
          }
          bool isInd = false;
          for (auto & c : chcs[i].srcRelations)
          {
            if (c == rel)
            {
              isInd = true;
              break;
            }
          }
          if (isInd)
          {
            indexes.push_back(i);
          }
          else
          {
            indexes.clear();
            return false;
          }
        }
      }
      return indexes.size() > 0;
    }

    void computeIncms()
    {
      incms.clear();
      for (int i = 0; i < chcs.size(); i++)
        incms[chcs[i].dstRelation].push_back(i);
    }

    void prune ()
    {
        int sz = decls.size();
        set<int> toSkip;
        computeIncms();

        for (auto it = decls.begin(); it != decls.end(); )
        {
          Expr d = *it;

          vector<int> indexes;
          bool toDel = hasOnlyInduct(d->left(), indexes);
          for (int i : indexes) toSkip.insert(i);

          if (toDel || incms[d->left()].empty())
          {
            toDel = true;
            for (int i = 0; i < chcs.size(); i++)
            {
              bool isInBody = false;
              for (auto & s : chcs[i].srcRelations)
              {
                if (s == d->left())
                {
                  isInBody = true;
                  break;
                }
              }
              if (isInBody)
              {
                toSkip.insert(i);
              }
            }
          }

          if (toDel) it = decls.erase(it);
          else ++it;
        }
        for (auto rit = toSkip.rbegin(); rit != toSkip.rend(); rit++) {
          chcs.erase(chcs.begin() + *rit);
        }

        if (sz == decls.size()) return;
        else prune();
    }

    void parse(string smt, string contract, bool removeQuery = false)
    {
      // GF: this entry part is different from the original implementation
      // (since the fixpoint format does not support ADTs)
//      Expr e = z3_from_smtlib_file (m_z3, smt_file);
//      for (auto & a : m_z3.getAdtConstructors()) {
//        constructors.push_back(regularizeQF(a));
//      }
//      ExprSet cnjs;
//      getConj(e, cnjs);
//      unitPropagation(cnjs);

      if (debug > 0) outs () << "\nPARSING" << "\n=======\n";
      std::unique_ptr<ufo::ZFixedPoint <EZ3> > m_fp;
      m_fp.reset (new ZFixedPoint<EZ3> (m_z3));
      ZFixedPoint<EZ3> &fp = *m_fp;
      fp.loadFPfromFile(smt);
      chcs.reserve(fp.m_rules.size());

      ExprMap eqs;
      for (auto it = fp.m_rules.begin(); it != fp.m_rules.end(); )
      {
        if (isOpX<EQ>(*it))
        {
          eqs[(*it)->left()->left()] = (*it)->right()->left();
          it = fp.m_rules.erase(it);
        }
        else ++it;
      }


      for (auto &r: fp.m_rules)
      {
        chcs.push_back(HornRuleExt());
        HornRuleExt& hr = chcs.back();
        while (true)
        {
          auto r1 = replaceAll(r, eqs);
          if (r == r1) break;
          else r = r1;
        }

        if (!normalize(r, hr))
        {
          chcs.pop_back();
          continue;
        }

//        filter (r, bind::IsConst(), inserter (origVrs, origVrs.begin()));
        // small rewr:
        if (isOpX<ITE>(r->last()))
        {
          hr.body = mk<IMPL>(mk<AND>(r->left(), r->last()->left()),
                             r->last()->right());
          chcs.push_back(chcs.back());
          chcs.back().body = mk<IMPL>(mk<AND>(r->left(), mkNeg(r->last()->left())),
                                      r->last()->last());
        }
        else
        {
          hr.body = r;
        }
      }


      for (auto it = chcs.begin(); it != chcs.end();)
      {
        HornRuleExt & hr = *it;
        hr.head = hr.body->right();
        hr.body = hr.body->left();
        if (isOpX<FAPP>(hr.head))
        {
          if (hr.head->left()->arity() == 2) {
//              (find(fp.m_queries.begin(), fp.m_queries.end(), hr.head) !=
//               fp.m_queries.end()))
            if (!addFailDecl(hr.head->left()->left())) {
              it = chcs.erase(it);
              continue;
            }
          }
          else
            addDecl(hr.head->left());


          hr.dstRelation = hr.head->left()->left();
//
//          for (auto it = hr.head->args_begin()+1; it != hr.head->args_end(); ++it)
//            hr.dstVars.push_back(*it); // to be rewritten later
        }
        else
        {
          if (!isOpX<FALSE>(hr.head)) hr.body = mk<AND>(hr.body, mk<NEG>(hr.head));
          if (!addFailDecl(mk<FALSE>(m_efac))) {
            it = chcs.erase(it);
            continue;
          }
          //          addFailDecl(mk<FALSE>(m_efac));
          hr.dstRelation = mk<FALSE>(m_efac);
        }
        ++it;
      }

      //TODO: Taken preprocessing from rnd, main cycle below not changed yet

      for (auto it = chcs.begin(); it != chcs.end();)
      {
        ExprVector origSrcSymbs, origDstSymbs;
        ExprSet lin;
        HornRuleExt & hr = *it;



        Expr head = hr.head;
        Expr body = hr.body;

        splitBody(hr, origSrcSymbs, lin);

        hr.isFact = hr.srcRelations.empty();
//        if (!)
//        {
//          outs() << "Removed: " << body << " => " << head << "\n";
//          it = chcs.erase(it);
//          continue;
//        }

        if (hr.srcRelations.size() == 0)
        {
          if (hasUninterp(body))
          {
            lin.clear();
          }
        }




//        if (isOpX<FAPP>(head))
//        {
//          if (head->arg(0)->arity() == 2 && !hr.isFact)
//          {
//            if (!addFailDecl(head->arg(0)->arg(0)))
//            {
//              it = chcs.erase(it);
//              continue;
//            }
//          }
//          else
//          {
//            addDecl(head->arg(0));
//          }
//          hr.head = head->arg(0);
//          hr.dstRelation = hr.head->arg(0);
//        }
//        else
//        {
//          if (!isOpX<FALSE>(head)) body = mk<AND>(body, mk<NEG>(head));
//
//          if (!addFailDecl(mk<FALSE>(m_efac)))
//          {
//            it = chcs.erase(it);
//            continue;
//          }
//          hr.dstRelation = mk<FALSE>(m_efac);
//        }


        hr.isQuery = (hr.dstRelation == failDecl);
        if (hr.isQuery)
        {
          it = chcs.erase(it);
          continue;
        }
        ++it;
        hr.isInductive = (hr.srcRelations.size() == 1 && hr.srcRelations[0] == hr.dstRelation);
        if (hr.isQuery) qCHCNum = chcs.size() - 1;
        ExprVector allOrigSymbs;
        for (auto & a : origSrcSymbs)  allOrigSymbs.push_back(a);
        if (!hr.isQuery)
        {
          for (auto it1 = head->args_begin()+1, end = head->args_end(); it1 != end; ++it1)
            origDstSymbs.push_back(*it1);
        }
        allOrigSymbs.insert(allOrigSymbs.end(), origDstSymbs.begin(), origDstSymbs.end());
        // simplBoolReplCnj(allOrigSymbs, lin); // perhaps, not a very important optimization now; consider removing
        //        origDstSymbs = hr.dstVars;
        if (isOpX<FAPP>(hr.head))
        {
          hr.head = head->left();
        }
        hr.body = conjoin(lin, m_efac);
        hr.dstVars.clear();


        vector<ExprVector> tmp;
        // we may have several applications of the same predicate symbol in the body:
        for (int i = 0; i < hr.srcRelations.size(); i++)
        {
          auto & a = hr.srcRelations[i];
          ExprVector tmp1;
          for (int j = 0; j < i; j++)
          {
            if (hr.srcRelations[i] == hr.srcRelations[j])
            {
              for (int k = 0; k < invVars[a].size(); k++)
              {
                Expr new_name = mkTerm<string> (varname + to_string(++total_var_cnt), m_efac);
                tmp1.push_back(cloneVar(invVars[a][k], new_name));
              }
              break;
            }
          }
          if (tmp1.empty())
          {
            tmp1 = invVars[a];
          }
          tmp.push_back(tmp1);
        }


        hr.assignVarsAndRewrite (origSrcSymbs, tmp,
                                 origDstSymbs, invVars[hr.dstRelation]);

        ExprVector body_vars;
        expr::filter (hr.body, bind::IsConst(), std::inserter (body_vars, body_vars.begin ()));
        for (auto it1 = hr.locVars.begin(); it1 != hr.locVars.end(); )
        {
          if (find(body_vars.begin(), body_vars.end(), *it1) == body_vars.end())
            it1 = hr.locVars.erase(it1);
          else ++it1;
        }
        outs() << "Chc: " << hr.body << " => " << hr.head << "\n";
      }

      for (int i = 0; i < chcs.size(); i++) {
        expr_id[chcs[i].dstRelation] = i;
        incms[chcs[i].dstRelation].push_back(i);
      }

//      for (int i = 0; i < chcs.size(); i++) {
//        outs() << "Chc " << i << " :" << chcs[i].body << " => "  << chcs[i].head << "\n";
//      }
      prune();

//      outs() << "Post pruning assignments: \n";
//      for (int i = 0; i < chcs.size(); i++) {
//        outs() << "Chc " << i << " :" << chcs[i].body  << "=>"  << chcs[i].head << "\n";
//      }
      index_fact_chc = -1;
      // find: index_cycle_chc
      for (int i = 0; i < chcs.size(); i++)
      {
        string name = lexical_cast<string>(chcs[i].dstRelation);
        if (name.find("nondet_interface") == std::string::npos &&
            find (chcs[i].srcRelations.begin(), chcs[i].srcRelations.end(),
            chcs[i].dstRelation) != chcs[i].srcRelations.end() &&
            name.find(contract) != std::string::npos)
        {
          index_cycle_chc.push_back(i);
          outs () << "cycle found (#" << i << "):\n";
          print(chcs[i]);
        }
      }

      assert(!index_cycle_chc.empty());

      // find fact now:
      for (int i = 0; i < chcs.size(); i++) {
        if (find(index_cycle_chc.begin(), index_cycle_chc.end(), i) !=
            index_cycle_chc.end())
          continue;
        if (chcs[i].dstRelation == chcs[index_cycle_chc[0]].dstRelation) {
          index_fact_chc = i;
          outs() << "fact found (#" << i << "):\n";
          print(chcs[i]);
          break;
        }
      }
    }

    vector<vector<int>> cur_batch;
    void findCombs(int num, vector<vector<int>>& res)
    {
      if (num == 1)
      {
        for (int i : index_cycle_chc)
        {
          vector<int> v2 = {i};
          res.push_back(v2);
        }
      }
      else
      {
        findCombs(num - 1, res);
        vector<vector<int>> res2;
        for (auto & v : res)
        {
          for (int i : index_cycle_chc)
          {
            vector<int> v2 = v;
            v2.push_back(i);
            res2.push_back(v2);
          }
        }
        res = res2;
      }
    }

    int getNumQs()
    {
      int i = 0;
      for (auto & c : chcs)
        i += c.isQuery;
      return i;
    }

    std::tuple<bool, ExprVector> mkNewQuery(int cycl_num)
    {
      outs () << "  ***************   pop back the query ************\n";
      if (chcs.back().isQuery)
        chcs.pop_back(); // important: kill the query created in `mkNewQuery`
      outs () << "mkNewQuery: " << cur_batch.size() << "; chcs " << chcs.size() << "\n";

      if (cur_batch.empty())
      {
        outs () << "  cur_batch empt: " << cycl_num << "\n";
        findCombs(cycl_num, cur_batch);
      }

      // outs () << "to copy: " << cy.srcRelations[sum] << "\n";
      chcs.push_back(chcs[index_fact_chc]);
      auto & hr = chcs.back();
//      pprint(chcs.back().body);
      int loc = 0;
      ExprVector newbody;
      ExprVector& prevdst = chcs[index_fact_chc].dstVars;
      Expr prevbody = chcs[index_fact_chc].body;

      for (int i = 0; i < cycl_num; i++)
      {
        auto & cy = chcs[cur_batch.back()[i]];

        int sum = 0, tr = 0;
        for (; sum < cy.srcRelations.size(); sum++)
          if (cy.srcRelations[sum] != cy.dstRelation)
            break;
        for (; tr < cy.srcRelations.size(); tr++)
          if (cy.srcRelations[tr] == cy.dstRelation)
            break;
        ExprVector& cursrc = cy.srcVars[tr];

        // outs () << "\n\ncopy " << i << "\n";

        ExprMap repl1, repl2, repl3;
        for (int k = 0; k < prevdst.size(); k++)
        {
          auto newvar = mkTerm<string> ("_bnd" + to_string(loc), m_efac);
          newvar = cloneVar(prevdst[k], newvar);
          repl1[prevdst[k]] = newvar;
          repl2[cursrc[k]] = newvar;
          loc++;
        }
        for (int k = 0; k < cy.locVars.size(); k++)
        {
          auto newvar = mkTerm<string> ("_loc" + to_string(loc), m_efac);
          newvar = cloneVar(cy.locVars[k], newvar);
          repl2[cy.locVars[k]] = newvar;
          loc++;
        }
//        pprint(prevbody);
//        pprint(cy.body);
        prevbody = replaceAll(prevbody, repl1);
//        pprint(prevbody);
        newbody.push_back(prevbody);
        // pprint(prevbody);
        prevbody = replaceAll(cy.body, repl2);
//        pprint(prevbody);
        prevdst = cy.dstVars;

        hr.srcRelations.push_back(cy.srcRelations[sum]);
        hr.srcVars.push_back(ExprVector());
        ExprVector vars;
        for (auto & v : cy.srcVars[sum])
        {
          auto newvar = mkTerm<string> (varname + to_string(total_var_cnt), m_efac);
          newvar = cloneVar(v, newvar);
          repl3[v] = newvar;
          hr.srcVars.back().push_back(newvar);
          total_var_cnt++;
        }
        prevbody = replaceAll(prevbody, repl3);
      }
      newbody.push_back(prevbody);
      hr.body = conjoin(newbody, m_efac);
//      pprint(chcs.back().body);
//      pprint(hr.body);
      hr.isQuery = 1;
      hr.isInductive = 0;
      hr.isFact = 0;
      hr.dstRelation = failDecl;
      hr.dstVars.clear();
      outs () << "   >>> new query:   ";
      ExprVector full_srcRelations = hr.srcRelations;
      pprint(hr.srcRelations);
      outs () << "\n";
//      if(full_srcRelations.size() > 2) {
//        hr.srcRelations = {full_srcRelations[full_srcRelations.size() - 1]};
//      }
      assert (!cur_batch.empty());
      cur_batch.pop_back();
      return {cur_batch.empty(), full_srcRelations};
    }

    void print_parse_results(){
      outs() << "chcs \n";
      for (int i = 0; i < chcs.size(); i++){
        outs() << i << " srs: ";
        for (int j = 0; j < chcs[i].srcRelations.size(); j++) {
          outs() << " " <<chcs[i].srcRelations[j]->getId();
        }
        outs() << " dst: " << chcs[i].dstRelation->getId() << " : "
        << chcs[i].dstRelation << " isQuery : " << chcs[i].isQuery << "\n";
      }
      for (auto i : index_cycle_chc)
        outs() << "index_cycle_chc : " << i << "\n";
      int i = 0;
      outs() << "decls \n";
      for (auto d: decls){
        outs() << i << " left: " << d->left()->getId() << " right: " << d->right()->getId() << "\n";
        i++;
      }
      i = 0;
      outs() << "expr_id \n";
      for (auto e: expr_id){
        outs() << i << " first: " << e.first->getId() << " second: " << e.second;
        outs() << "\n";
        i++;
      }
    }

      void unitPropagation(ExprSet &cnjs) {
        ExprMap matching;
        for  (auto &r: cnjs) {
          if (isOpX<NEG>(r) && r->arity() == 1 && !isOpX<FALSE>(r->left())) {
            matching[r->left()] = mk<FALSE>(m_efac);
          }
        }
        if (matching.empty()) {
          return;
        }
        else {
          ExprSet newCnjs;
          for  (auto &r: cnjs) {
            Expr r1 = replaceAll(r, matching);
            newCnjs.insert(r1);
          }
          cnjs = newCnjs;
          unitPropagation(cnjs);
        }
      }


      bool addFailDecl(Expr decl)
    {
      if (failDecl == NULL)
      {
        failDecl = decl;
      }
      else
      {
        if (failDecl != decl)
        {
          //TODO:support
          // errs () << "Multiple queries are not supported\n";
          //exit(0);
          return false;
        }
      }
      return true;
    }

    Expr getPostcondition (int i)
    {
      HornRuleExt& hr = chcs[i];
      ExprSet cnjs;
      ExprSet newCnjs;
      getConj(hr.body, cnjs);
      ExprVector allVars = hr.locVars;
      for (auto & a : hr.srcVars) allVars.insert(allVars.end(), a.begin(), a.end());
      for (auto & a : cnjs)
      {
        if (emptyIntersect(a, allVars)) newCnjs.insert(a);
      }
      return conjoin(newCnjs, m_efac);
    }

    void print()
    {
      outs() << "CHCs:\n";
      for (auto &hr: chcs) print(hr);
    }

    void print(HornRuleExt& hr, bool full = false)
    {
        if (hr.isFact) outs() << "  INIT:\n";
        if (hr.isInductive) outs() << "  TRANSITION RELATION:\n";
        if (hr.isQuery) outs() << "  BAD:\n";

        outs () << "    ";

        for (int i = 0; i < hr.srcRelations.size(); i++)
        {
          outs () << * hr.srcRelations[i];
          if (full)
          {
             outs () << " srcRelations: (";
              for(auto &a: hr.srcVars[i]) outs() << *a << ", ";
                outs () << "\b\b)";
          }
          outs () << " /\\ ";
        }
        outs () << "\b\b\b\b  [arity " << hr.srcRelations.size()<< "] -> " << * hr.dstRelation << "\n";

        if (full)
        {
          if (hr.dstVars.size() > 0)
          {
            outs () << " dstVars: (";
            for(auto &a: hr.dstVars) outs() << *a << ", ";
            outs () << "\b\b)";
          }
          outs() << "\n    body: " << * hr.body << "\n";

          if (hr.locVars.size() > 0)
          {
            outs () << " locVars: (";
            for(auto &a: hr.locVars) outs() << *a << ", ";
            outs () << "\b\b)\n";
          }
        }
    }

  };
}
#endif
