#include <fastsynth/incremental_prop_learn.h>
#include <fastsynth/synth_encoding_constraints.h>

#include <solvers/flattening/bv_pointers.h>

#include <minisat/simp/SimpSolver.h>
#include <minisat/core/Solver.h>

template <class satcheckt>
incremental_prop_learnt<satcheckt>::incremental_prop_learnt(
  messaget &msg,
  const namespacet &ns,
  const cegist::problemt &problem)
  : msg(msg),
    ns(ns),
    problem(problem),
    synth_satcheck(new cancellable_solvert<satcheckt>()),
    synth_solver(new bv_pointerst(ns, *synth_satcheck)),
    program_size(1u),
    counterexample_counter(0u)
{
  init();
}

template <class satcheckt>
void incremental_prop_learnt<satcheckt>::init()
{
  synth_encoding.program_size = program_size;
  synth_satcheck->set_message_handler(msg.get_message_handler());
  synth_solver->set_message_handler(msg.get_message_handler());

  generate_constraint(
    ns, get_message_handler(), problem, counterexamples,
    synth_encoding, *synth_solver);

  freeze_expression_symbols();
}

template <class satcheckt>
void incremental_prop_learnt<satcheckt>::set_program_size(
  const size_t program_size)
{
  PRECONDITION(program_size >= this->program_size);
  if(program_size == this->program_size)
    return;
  this->program_size = program_size;

  synth_satcheck.reset(new cancellable_solvert<satcheckt>());
  synth_solver.reset(new bv_pointerst(ns, *synth_satcheck));
  synth_encoding = synth_encodingt();
  init();
}

template <class satcheckt>
decision_proceduret::resultt incremental_prop_learnt<satcheckt>::operator()()
{
  synth_satcheck->clear();
  return (*synth_solver)();
}

template <class satcheckt>
std::map<symbol_exprt, exprt>
incremental_prop_learnt<satcheckt>::get_expressions() const
{
  return synth_encoding.get_expressions(*synth_solver);
}

template <class satcheckt>
void incremental_prop_learnt<satcheckt>::add(
  const verify_encodingt::counterexamplet &counterexample)
{
  counterexamples.emplace_back(counterexample);

  synth_encoding.constraints.clear();

  synth_encoding.suffix = "$ce" + std::to_string(counterexample_counter);

  add_counterexample(ns, get_message_handler(), counterexample, synth_encoding, *synth_solver);
  add_problem(ns, get_message_handler(), problem, synth_encoding, *synth_solver);

  freeze_expression_symbols();
  counterexample_counter++;
}

template <class satcheckt>
void incremental_prop_learnt<satcheckt>::cancel()
{
  synth_satcheck->cancel();
}
