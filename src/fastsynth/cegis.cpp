#include "cegis.h"
#include "synth_encoding.h"
#include "verify_encoding.h"

#include <langapi/language_util.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include <goto-symex/goto_symex.h>
#include <goto-symex/symex_target_equation.h>

#include <util/simplify_expr.h>

decision_proceduret::resultt cegist::operator()(
  symex_target_equationt &equation)
{
  return non_incremental_loop(equation);
}

decision_proceduret::resultt cegist::non_incremental_loop(
  symex_target_equationt &equation)
{
  status() << "** non-incremental CEGIS" << eom;

  unsigned iteration=0;

  std::size_t program_size=1;

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
    synth_encoding.program_size=program_size;

    if(counterexamples.empty())
    {
      synth_encoding.suffix="$ce";
      synth_encoding.constraints.clear();
      convert_negation(equation, synth_encoding, synth_solver);

      for(const auto &c : synth_encoding.constraints)
      {
        synth_solver.set_to_true(c);
        debug() << "ec: " << from_expr(ns, "", c) << eom;
      }
    }
    else
    {
      std::size_t counter=0;
      for(const auto &c : counterexamples)
      {
        synth_encoding.suffix="$ce"+std::to_string(counter);
        synth_encoding.constraints.clear();
        add_counterexample(c, synth_encoding, synth_solver);
        convert_negation(equation, synth_encoding, synth_solver);

        for(const auto &c : synth_encoding.constraints)
        {
          synth_solver.set_to_true(c);
          debug() << "ec: " << from_expr(ns, "", c) << eom;
        }

        counter++;
      }
    }

    switch(synth_solver())
    {
    case decision_proceduret::resultt::D_SATISFIABLE: // got candidate
      {
        std::map<symbol_exprt, exprt> old_expressions;
        old_expressions.swap(expressions);

        #if 0
        synth_solver.print_assignment(debug());
        debug() << eom;
        #endif

        expressions=synth_encoding.get_expressions(synth_solver);

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

    convert(equation, verify_encoding, verify_solver);

    switch(verify_solver())
    {
    case decision_proceduret::resultt::D_SATISFIABLE: // counterexample
      counterexamples.push_back(verify_encoding.get_counterexample(verify_solver));
      break;

    case decision_proceduret::resultt::D_UNSATISFIABLE: // done, got solution
      status() << "Result obtained with " << iteration << " iteration(s)" << eom;
      result() << "VERIFICATION SUCCESSFUL" << eom;
      return decision_proceduret::resultt::D_SATISFIABLE;

    case decision_proceduret::resultt::D_ERROR:
      return decision_proceduret::resultt::D_ERROR;
    }

  }
}

decision_proceduret::resultt cegist::incremental_loop(
  symex_target_equationt &equation)
{
  status() << "** incremental CEGIS" << eom;

  unsigned iteration=0;

  std::size_t program_size=1;
  std::size_t counterexample_counter=0;

  // now enter the CEGIS loop
  while(true)
  {
    satcheck_no_simplifiert synth_satcheck;
    synth_satcheck.set_message_handler(get_message_handler());

    bv_pointerst synth_solver(ns, synth_satcheck);
    synth_solver.set_message_handler(get_message_handler());

    synth_encodingt synth_encoding;
    synth_encoding.program_size=program_size;

    convert_negation(equation, synth_encoding, synth_solver);

    bool verify=false;

    do
    {
      iteration++;
      status() << "** CEGIS iteration " << iteration << eom;

      status() << "** Synthesis phase" << eom;

      switch(synth_solver())
      {
      case decision_proceduret::resultt::D_SATISFIABLE: // got candidate
        {
          std::map<symbol_exprt, exprt> old_expressions;
          old_expressions.swap(expressions);

          #if 0
          synth_solver.print_assignment(debug());
          debug() << eom;
          #endif

          expressions=synth_encoding.get_expressions(synth_solver);

          for(auto &e : expressions)
            e.second=simplify_expr(e.second, ns);

          if(old_expressions==expressions)
          {
            error() << "NO PROGRESS MADE" << eom;
            return decision_proceduret::resultt::D_ERROR;
          }
        }

        verify=true;
        break;

      case decision_proceduret::resultt::D_UNSATISFIABLE: // no candidate
        if(program_size<5)
        {
          program_size+=1;
          status() << "Failed to get candidate; "
                      "increasing program size to " << program_size << eom;
          verify=false; // do another attempt to synthesize
          break;
        }

        error() << "FAILED TO GET CANDIDATE" << eom;
        return decision_proceduret::resultt::D_UNSATISFIABLE;

      case decision_proceduret::resultt::D_ERROR:
        return decision_proceduret::resultt::D_ERROR;
      }

      if(verify)
      {
        status() << "** Verification phase" << eom;

        output_expressions(expressions, ns, debug());
        debug() << eom;

        satcheckt verify_satcheck;
        verify_satcheck.set_message_handler(get_message_handler());

        bv_pointerst verify_solver(ns, verify_satcheck);
        verify_solver.set_message_handler(get_message_handler());

        verify_encodingt verify_encoding;
        verify_encoding.expressions=expressions;

        convert(equation, verify_encoding, verify_solver);

        switch(verify_solver())
        {
        case decision_proceduret::resultt::D_SATISFIABLE: // counterexample
          {
            auto c=verify_encoding.get_counterexample(verify_solver);

            synth_encoding.suffix=
              "$ce"+std::to_string(counterexample_counter);
            add_counterexample(c, synth_encoding, synth_solver);
            convert_negation(equation, synth_encoding, synth_solver);
            counterexample_counter++;
          }
          break;

        case decision_proceduret::resultt::D_UNSATISFIABLE: // done, got solution
          status() << "Result obtained with " << iteration << " iteration(s)" << eom;
          result() << "VERIFICATION SUCCESSFUL" << eom;
          return decision_proceduret::resultt::D_SATISFIABLE;

        case decision_proceduret::resultt::D_ERROR:
          return decision_proceduret::resultt::D_ERROR;
        }
      }
    }
    while(verify);
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

void cegist::convert(
  symex_target_equationt &equation,
  verify_encodingt &verify_encoding,
  prop_convt &prop_conv)
{
  // guards
  for(auto &step : equation.SSA_steps)
    step.guard_literal=prop_conv.convert(verify_encoding(step.guard));

  // assignments
  for(const auto &step : equation.SSA_steps)
    if(step.is_assignment())
    {
      exprt encoded=verify_encoding(step.cond_expr);
      debug() << "pa: " << from_expr(ns, "", encoded) << eom;
      prop_conv.set_to_true(encoded);
    }

  // decls
  for(const auto &step : equation.SSA_steps)
    if(step.is_decl())
      prop_conv.convert(verify_encoding(step.cond_expr));

  // gotos
  for(auto &step : equation.SSA_steps)
    if(step.is_goto())
      step.cond_literal=prop_conv.convert(verify_encoding(step.cond_expr));

  // now do assertions and assumptions
  exprt::operandst assumptions, assertions;

  for(auto &step : equation.SSA_steps)
  {
    if(step.is_assume())
    {
      exprt encoded=verify_encoding(step.cond_expr);
      debug() << "pA: " << from_expr(ns, "", encoded) << eom;
      literalt l=prop_conv.convert(encoded);
      step.cond_literal=l;
      assumptions.push_back(literal_exprt(l));
    }
    else if(step.is_assert())
    {
      exprt encoded=verify_encoding(step.cond_expr);
      debug() << "pr: " << from_expr(ns, "", encoded) << eom;
      assertions.push_back(
        implies_exprt(conjunction(assumptions), encoded));
    }
  }

  // one assertion must be false
  prop_conv.set_to_false(conjunction(assertions));
}

void cegist::add_counterexample(
  const counterexamplet &ce,
  synth_encodingt &synth_encoding,
  prop_convt &prop_conv)
{
  for(const auto &it : ce)
  {
    const exprt &symbol=it.first;
    const exprt &value=it.second;

    exprt encoded=synth_encoding(equal_exprt(symbol, value));
    debug() << "ce: " << from_expr(ns, "", encoded) << eom;
    prop_conv.set_to_true(encoded);
  }
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
