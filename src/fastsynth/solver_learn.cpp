#include <fastsynth/solver_learn.h>
#include <fastsynth/synth_encoding.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#include <langapi/language_util.h>

#include "fourier_motzkin.h"

prop_learn_baset::prop_learn_baset(
  const namespacet &_ns,
  const cegist::problemt &_problem,
  message_handlert &_message_handler):
  learnt(_message_handler), ns(_ns), problem(_problem)
{
}

void prop_learn_baset::add_counterexample(
  const verify_encodingt::counterexamplet &ce,
  synth_encodingt &synth_encoding,
  decision_proceduret &solver)
{
  for(const auto &it : ce)
  {
    const exprt &symbol = it.first;
    const exprt &value = it.second;

    exprt encoded = synth_encoding(equal_exprt(symbol, value));
    debug() << "ce: " << from_expr(ns, "", encoded) << eom;
    solver.set_to_true(encoded);
  }
}

void prop_learn_baset::add_problem(
  synth_encodingt &encoding,
  decision_proceduret &solver)
{
  for(const exprt &e : problem.side_conditions)
  {
    const exprt encoded = encoding(e);
    debug() << "sc: " << from_expr(ns, "", encoded) << eom;
    solver.set_to_true(encoded);
  }

  for(const auto &e : problem.constraints)
  {
    const exprt encoded = encoding(e);
    debug() << "co: " << from_expr(ns, "", encoded) << eom;
    solver.set_to_true(encoded);
  }

  for(const auto &c : encoding.constraints)
  {
    solver.set_to_true(c);
    debug() << "ec: " << from_expr(ns, "", c) << eom;
  }
}

prop_learnt::prop_learnt(
  const namespacet &_ns,
  const cegist::problemt &_problem,
  message_handlert &_message_handler):
  prop_learn_baset(_ns, _problem, _message_handler),
  program_size(1u)
{
}

void prop_learnt::set_program_size(const size_t program_size)
{
  this->program_size = program_size;
}

decision_proceduret::resultt prop_learnt::operator()()
{
  {
    satcheckt fm_satcheck;
    fourier_motzkint fm_solver(ns, fm_satcheck);
    fm_solver.set_message_handler(get_message_handler());
    synth_encodingt synth_encoding;
    synth_encoding.program_size = program_size;
    add_problem(synth_encoding, fm_solver);
    fm_solver();
  }

  satcheckt synth_satcheck;
  synth_satcheck.set_message_handler(get_message_handler());

  bv_pointerst synth_solver(ns, synth_satcheck);
  synth_solver.set_message_handler(get_message_handler());

  synth_encodingt synth_encoding;
  synth_encoding.program_size = program_size;

  if(counterexamples.empty())
  {
    synth_encoding.suffix = "$ce";
    synth_encoding.constraints.clear();

    add_problem(synth_encoding, synth_solver);
  }
  else
  {
    std::size_t counter = 0;
    for(const auto &c : counterexamples)
    {
      synth_encoding.suffix = "$ce" + std::to_string(counter);
      synth_encoding.constraints.clear();
      add_counterexample(c, synth_encoding, synth_solver);

      add_problem(synth_encoding, synth_solver);

      counter++;
    }
  }

  const decision_proceduret::resultt result(synth_solver());
  if(decision_proceduret::resultt::D_SATISFIABLE == result)
    last_solution = synth_encoding.get_expressions(synth_solver);

  return result;
}

std::map<symbol_exprt, exprt> prop_learnt::get_expressions() const
{
  return last_solution;
}

void prop_learnt::add(const verify_encodingt::counterexamplet &counterexample)
{
  counterexamples.emplace_back(counterexample);
}
