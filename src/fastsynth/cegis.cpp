#include "cegis.h"
#include "verify_solver.h"
#include "synth_solver.h"

#include <langapi/language_util.h>

#include <solvers/sat/satcheck.h>

#include <goto-symex/goto_symex.h>
#include <goto-symex/symex_target_equation.h>

decision_proceduret::resultt cegist::operator()(
  symex_target_equationt &equation)
{
  unsigned iteration=0;
  
  // now enter the CEGIS loop
  while(true)
  {
    iteration++;
    status() << "CEGIS iteration " << iteration << eom;
    
    for(const auto &e : expressions)
      debug() << e.first.function().get_identifier()
              << " -> " << from_expr(ns, "", e.second) << eom;

    status() << "Verification phase" << eom;

    satcheckt verify_satcheck;
    verify_solvert verify_solver(ns, verify_satcheck);
    verify_satcheck.set_message_handler(get_message_handler());
    verify_solver.set_message_handler(get_message_handler());
    verify_solver.expressions=expressions;

    equation.convert(verify_solver);

    switch(verify_solver())
    {
    case decision_proceduret::resultt::D_SATISFIABLE: // counterexample
      break;

    case decision_proceduret::resultt::D_UNSATISFIABLE: // done, got solution
      result() << "VERIFICATION SUCCESSFUL" << eom;
      return decision_proceduret::resultt::D_SATISFIABLE;

    case decision_proceduret::resultt::D_ERROR:
      return decision_proceduret::resultt::D_ERROR;
    }
    
    status() << "Synthesis phase" << eom;

    satcheckt synth_satcheck;
    synth_solvert synth_solver(ns, synth_satcheck);
    synth_satcheck.set_message_handler(get_message_handler());
    synth_solver.set_message_handler(get_message_handler());

    convert_negation(equation, synth_solver);

    switch(synth_solver())
    {
    case decision_proceduret::resultt::D_SATISFIABLE: // got candidate
      {
        std::map<function_application_exprt, exprt> old_expressions;
        old_expressions.swap(expressions);
        expressions=synth_solver.get_expressions();
        if(old_expressions==expressions)
        {
          error() << "NO PROGRESS MADE" << eom;
          return decision_proceduret::resultt::D_ERROR;
        }
      }
      break;

    case decision_proceduret::resultt::D_UNSATISFIABLE: // no candidate
      error() << "FAILED TO GET CANDIDATE" << eom;
      return decision_proceduret::resultt::D_UNSATISFIABLE;

    case decision_proceduret::resultt::D_ERROR:
      return decision_proceduret::resultt::D_ERROR;
    }
  }
}

void cegist::convert_negation(
  symex_target_equationt &equation,
  prop_convt &prop_conv)
{
  // all but assertions and assumptions
  equation.convert_guards(prop_conv);
  equation.convert_assignments(prop_conv);
  equation.convert_decls(prop_conv);
  equation.convert_goto_instructions(prop_conv);
  equation.convert_io(prop_conv);
  equation.convert_constraints(prop_conv);  
  
  // now do assertions and assumptions
  for(auto &step : equation.SSA_steps)
  {
    if(step.is_assert() ||
       step.is_assume())
    {
      prop_conv.set_to_true(step.cond_expr);
      step.cond_literal=const_literal(true);
    }
  }
}

