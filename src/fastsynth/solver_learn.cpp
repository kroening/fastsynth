#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#include <langapi/language_util.h>

#include "synth_encoding.h"
#include "solver_learn.h"

solver_learn_baset::solver_learn_baset(
  const namespacet &_ns,
  const problemt &_problem,
  message_handlert &_message_handler):
  learnt(_message_handler), ns(_ns), problem(_problem)
{
}

void solver_learn_baset::add_counterexample(
  const counterexamplet &ce,
  synth_encodingt &synth_encoding,
  decision_proceduret &solver)
{
  for(const auto &it : ce.assignment)
  {
    const exprt &symbol = it.first;
    const exprt &value = it.second;

    exprt encoded = synth_encoding(equal_exprt(symbol, value));
    debug() << "ce: " << from_expr(ns, "", encoded) << eom;
    solver.set_to_true(encoded);
  }
}

void solver_learn_baset::add_problem(
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

solver_learnt::solver_learnt(
  const namespacet &_ns,
  const problemt &_problem,
  message_handlert &_message_handler):
  solver_learn_baset(_ns, _problem, _message_handler),
  program_size(1u)
{
}

void solver_learnt::set_program_size(const size_t program_size)
{
  this->program_size = program_size;
}

decision_proceduret::resultt solver_learnt::operator()()
{
  satcheckt synth_satcheck;
  synth_satcheck.set_message_handler(get_message_handler());

  bv_pointerst synth_solver(ns, synth_satcheck);
  synth_solver.set_message_handler(get_message_handler());

  synth_encodingt synth_encoding;
  synth_encoding.program_size = program_size;
  synth_encoding.enable_bitwise = enable_bitwise;

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
    last_solution = synth_encoding.get_solution(synth_solver);

  return result;
}

solutiont solver_learnt::get_solution() const
{
  return last_solution;
}

void solver_learnt::add_ce(
  const counterexamplet &counterexample)
{
  counterexamples.emplace_back(counterexample);
}
