#include "cegis.h"
#include "composite_learn.h"
#include "incremental_prop_learn.h"
#include "prop_learn.h"
#include "synth_encoding.h"
#include "verify_encoding.h"

#include <langapi/language_util.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include <util/simplify_expr.h>

decision_proceduret::resultt cegist::operator()(
    const problemt &problem)
{
  composite_learnt learn;

  if(incremental_solving)
  {
    status() << "** incremental CEGIS" << eom;
    if(use_simp_solver)
      learn.add<incremental_prop_learnt<satcheckt>>(*this, ns, problem);
    else
      learn.add<incremental_prop_learnt<satcheck_no_simplifiert>>(
        *this, ns, problem);
  }
  else
  {
    status() << "** non-incremental CEGIS" << eom;
    learn.add<prop_learnt>(*this, ns, problem);
  }

  return loop(problem, learn);
}

decision_proceduret::resultt cegist::loop(
  const problemt &problem, learnt &learn)
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
        std::map<symbol_exprt, exprt> old_expressions;
        old_expressions.swap(expressions);

        #if 0
        synth_solver.print_assignment(debug());
        debug() << eom;
        #endif

        expressions=learn.get_expressions();

        for(auto &e : expressions)
          e.second=simplify_expr(e.second, ns);

        if(old_expressions==expressions)
        {
          error() << "NO PROGRESS MADE" << eom;
          return decision_proceduret::resultt::D_ERROR;
        }
      }
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

    output_expressions(expressions, ns, debug());
    debug() << eom;

    satcheckt verify_satcheck;
    verify_satcheck.set_message_handler(get_message_handler());

    bv_pointerst verify_solver(ns, verify_satcheck);
    verify_solver.set_message_handler(get_message_handler());

    verify_encodingt verify_encoding;
    verify_encoding.expressions=expressions;

    add_problem(problem, verify_encoding, verify_solver);

    switch(verify_solver())
    {
    case decision_proceduret::resultt::D_SATISFIABLE: // counterexample
      status() << "** Verification failed" << eom;
      learn.add(verify_encoding.get_counterexample(verify_solver));
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

void cegist::add_problem(
  const problemt &problem,
  verify_encodingt &encoding,
  prop_convt &prop_conv)
{
  for(const auto &e : problem.side_conditions)
  {
    const exprt encoded=encoding(e);
    debug() << "sc: " << from_expr(ns, "", encoded) << eom;
    prop_conv.set_to_true(encoded);
  }

  const exprt encoded=encoding(conjunction(problem.constraints));
  debug() << "co: !(" << from_expr(ns, "", encoded) << ')' << eom;
  prop_conv.set_to_false(encoded);
}

void output_expressions(
  const std::map<symbol_exprt, exprt> &expressions,
  const namespacet &ns,
  std::ostream &out)
{
  for(const auto &e : expressions)
  {
    out << e.first.get_identifier()
        << " -> "
        << from_expr(ns, "", e.second)
        << '\n';
  }
}
