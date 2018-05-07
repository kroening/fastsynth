#include "cegis.h"
#include "incremental_solver_learn.h"
#include "solver_learn.h"
#include "verify.h"
#include "fm_verify.h"
#include "enumerative_learn.h"
#include <langapi/language_util.h>

#include <util/simplify_expr.h>

#include <memory>

decision_proceduret::resultt cegist::operator()(
  const problemt &problem)
{
  std::unique_ptr<learnt> learner;
  std::unique_ptr<verifyt> verifier;

  if((incremental_solving || use_simp_solver) && use_smt)
  {
    warning() << "WARNING: unable to use smt back end and incremental solving together\n"
              << "Using smt only" << eom;
    incremental_solving=false;
    use_simp_solver=false;
  }
  if(logic=="LIA")
  {
    warning() << "WARNING: Linear Integer Arithmetic requires SMT backend. Using SMT back end" << eom;
    use_smt=true;
    use_simp_solver=false;
    incremental_solving=false;
  }

  if(incremental_solving)
  {
    status() << "** incremental CEGIS" << eom;
    learner=std::unique_ptr<learnt>(new incremental_solver_learnt(
      ns, problem, use_simp_solver, get_message_handler()));
  }
  else if(enumerative_engine)
  {
   status() << "** enumerative engine" << eom;
   learner=std::unique_ptr<learnt>(new enumerative_learnt(
       ns, problem, get_message_handler()));
  }
  else
  {
    status() << "** non-incremental CEGIS" << eom;
    solver_learnt *l=new solver_learnt(
      ns, problem, get_message_handler());

    l->use_smt=use_smt;
    l->logic=logic;

    learner=std::unique_ptr<learnt>(l);
  }

  learner->enable_bitwise=enable_bitwise;

  if(use_fm)
  {
    verifier=std::unique_ptr<verifyt>(new fm_verifyt(
      ns, problem, get_message_handler()));
  }
  else
  {
    verifier=std::unique_ptr<verifyt>(new verifyt(
      ns, problem, get_message_handler()));
  }

  verifier->use_smt=use_smt;
  verifier->logic=logic;

  return loop(problem, *learner, *verifier);
}

decision_proceduret::resultt cegist::loop(
  const problemt &problem,
  learnt &learn,
  verifyt &verify)
{
  unsigned iteration=0;

  std::size_t program_size=1;

  // now enter the CEGIS loop
  while(true)
  {
    iteration++;
    status() << "** CEGIS iteration " << iteration << eom;

    status() << "** Synthesis phase" << eom;

    learn.set_program_size(program_size);

    switch(learn())
    {
    case decision_proceduret::resultt::D_SATISFIABLE: // got candidate
      {
        std::map<symbol_exprt, exprt> old_functions;
        old_functions.swap(solution.functions);

        solution=learn.get_solution();

        for(auto &f : solution.functions)
          f.second=simplify_expr(f.second, ns);

        if(old_functions==solution.functions)
        {
          status()<<"size of old functions "<<old_functions.size()<<eom;
          for(const auto &expr: old_functions)
            status()<< from_expr(ns, "", expr.first)<<" "
                    << from_expr(ns, "", expr.second)<<eom;

          error() << "NO PROGRESS MADE" << eom;
          return decision_proceduret::resultt::D_ERROR;
        }
      }
      // proceed to verification phase
      break;

    case decision_proceduret::resultt::D_UNSATISFIABLE: // no candidate
      if(program_size<max_program_size)
      {
        program_size+=1;
        status() << "Failed to get candidate; "
                    "increasing program size to " << program_size << eom;
        continue; // do another attempt to synthesize
      }

      error() << "FAILED TO GET CANDIDATE" << eom;
      return decision_proceduret::resultt::D_UNSATISFIABLE;

    case decision_proceduret::resultt::D_ERROR:
      return decision_proceduret::resultt::D_ERROR;
    }

    status() << "** Verification phase" << eom;

    switch(verify(solution))
    {
    case decision_proceduret::resultt::D_SATISFIABLE: // counterexample
      status() << "** Verification failed" << eom;
      learn.add_ce(verify.get_counterexample());
      break;

    case decision_proceduret::resultt::D_UNSATISFIABLE: // done, got solution
      status() << "Result obtained with " << iteration << " iteration(s)"
               << eom;
      result() << "VERIFICATION SUCCESSFUL" << eom;
      return decision_proceduret::resultt::D_SATISFIABLE;

    case decision_proceduret::resultt::D_ERROR:
      return decision_proceduret::resultt::D_ERROR;
    }
  }
}

