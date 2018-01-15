#include <fastsynth/incremental_prop_learn.h>
#include <fastsynth/prop_learn.h>

#include <solvers/flattening/bv_pointers.h>

incremental_prop_learnt::incremental_prop_learnt(
  messaget &msg,
  const namespacet &ns,
  const cegist::problemt &problem)
  : msg(msg),
    ns(ns),
    problem(problem),
    synth_satcheck(new satcheck_no_simplifiert()),
    synth_solver(new bv_pointerst(ns, *synth_satcheck)),
    program_size(1u),
    counterexample_counter(0u)
{
  init();
}

void incremental_prop_learnt::init()
{
  synth_encoding.program_size = program_size;
  synth_satcheck->set_message_handler(msg.get_message_handler());
  synth_solver->set_message_handler(msg.get_message_handler());
  add_problem(ns, msg, problem, synth_encoding, *synth_solver);
}

void incremental_prop_learnt::set_program_size(const size_t program_size)
{
  PRECONDITION(program_size >= this->program_size);
  if(program_size == this->program_size)
    return;
  this->program_size = program_size;

  synth_satcheck.reset(new satcheck_minisat_no_simplifiert());
  synth_solver.reset(new bv_pointerst(ns, *synth_satcheck));
  synth_encoding = synth_encodingt();
  counterexample_counter = 0u;
  init();
}

decision_proceduret::resultt incremental_prop_learnt::operator()()
{
  return (*synth_solver)();
}

std::map<symbol_exprt, exprt> incremental_prop_learnt::get_expressions() const
{
  return synth_encoding.get_expressions(*synth_solver);
}

void incremental_prop_learnt::add(
  const verify_encodingt::counterexamplet &counterexample)
{
  synth_encoding.constraints.clear();

  synth_encoding.suffix = "$ce" + std::to_string(counterexample_counter);

  add_counterexample(ns, msg, counterexample, synth_encoding, *synth_solver);
  add_problem(ns, msg, problem, synth_encoding, *synth_solver);

  counterexample_counter++;
}
