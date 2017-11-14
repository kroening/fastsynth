#include "cegis.h"
#include "verify_solver.h"
#include "synth_encoding.h"

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
    status() << "** CEGIS iteration " << iteration << eom;
    
    status() << "** Synthesis phase" << eom;

    satcheckt synth_satcheck;
    synth_satcheck.set_message_handler(get_message_handler());

    bv_pointerst synth_solver(ns, synth_satcheck);
    synth_solver.set_message_handler(get_message_handler());

    synth_encodingt synth_encoding;

    if(counterexamples.empty())
    {
      convert_negation(equation, synth_encoding, synth_solver);
    }
    else
    {
      std::size_t counter=0;
      for(const auto &c : counterexamples)
      {
        synth_encoding.suffix="$ce"+std::to_string(counter);
        add_counterexample(c, synth_encoding, synth_solver);
        convert_negation(equation, synth_encoding, synth_solver);
        counter++;
      }
    }

    switch(synth_solver())
    {
    case decision_proceduret::resultt::D_SATISFIABLE: // got candidate
      {
        std::map<symbol_exprt, exprt> old_expressions;
        old_expressions.swap(expressions);

        expressions=synth_encoding.get_expressions(synth_solver);
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

    status() << "** Verification phase" << eom;

    for(const auto &e : expressions)
      debug() << e.first.get_identifier()
              << " -> " << from_expr(ns, "", e.second) << eom;

    satcheckt verify_satcheck;
    verify_satcheck.set_message_handler(get_message_handler());

    verify_solvert verify_solver(ns, verify_satcheck);
    verify_solver.set_message_handler(get_message_handler());
    verify_solver.expressions=expressions;

    equation.convert(verify_solver);

    switch(verify_solver())
    {
    case decision_proceduret::resultt::D_SATISFIABLE: // counterexample
      counterexamples.push_back(verify_solver.get_counterexample());
      break;

    case decision_proceduret::resultt::D_UNSATISFIABLE: // done, got solution
      result() << "VERIFICATION SUCCESSFUL" << eom;
      return decision_proceduret::resultt::D_SATISFIABLE;

    case decision_proceduret::resultt::D_ERROR:
      return decision_proceduret::resultt::D_ERROR;
    }

  }
}

void cegist::convert_negation(
  symex_target_equationt &equation,
  synth_encodingt &synth_encoding,
  prop_convt &prop_conv)
{
  // guards
  for(auto &step : equation.SSA_steps)
    step.guard_literal=prop_conv.convert(synth_encoding(step.guard));

  // assignments
  for(const auto &step : equation.SSA_steps)
    if(step.is_assignment())
    {
      exprt encoded=synth_encoding(step.cond_expr);
      debug() << "pa: " << from_expr(ns, "", encoded) << eom;
      prop_conv.set_to_true(encoded);
    }

  // decls
  for(const auto &step : equation.SSA_steps)
    if(step.is_decl())
      prop_conv.convert(synth_encoding(step.cond_expr));

  // gotos
  for(auto &step : equation.SSA_steps)
    if(step.is_goto())
      step.cond_literal=prop_conv.convert(synth_encoding(step.cond_expr));

  // now do assertions and assumptions
  for(auto &step : equation.SSA_steps)
  {
    if(step.is_assert() ||
       step.is_assume())
    {
      exprt encoded=synth_encoding(step.cond_expr);
      debug() << "pr: " << from_expr(ns, "", encoded) << eom;
      prop_conv.set_to_true(encoded);
      step.cond_literal=const_literal(true);
    }
  }
}

void cegist::add_counterexample(
  const counterexamplet &ce,
  synth_encodingt &synth_encoding,
  prop_convt &prop_conv)
{
  for(const auto &it : ce)
  {
    const function_application_exprt &app=it.first;
    const exprt::operandst &values=it.second;
    const auto &arguments=app.arguments();

    assert(arguments.size()==values.size());

    for(std::size_t i=0; i<arguments.size(); i++)
    {
      exprt encoded=synth_encoding(
        equal_exprt(arguments[i], values[i]));
      debug() << "ce: " << from_expr(ns, "", encoded) << eom;
      prop_conv.set_to_true(encoded);
    }
  }
}
