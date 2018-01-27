#include <fastsynth/synth_encoding.h>
#include <fastsynth/synth_encoding_constraints.h>

#include <solvers/flattening/bv_pointers.h>

#include <minisat/simp/SimpSolver.h>
#include <minisat/core/Solver.h>

template <class satcheckt>
incremental_prop_learnt<satcheckt>::incremental_prop_learnt(
  message_handlert &msg,
  const namespacet &ns,
  const cegist::problemt &problem,
  const synth_encoding_factoryt synth_encoding_factory)
  :ns(ns),
    problem(problem),
    synth_encoding_factory(synth_encoding_factory),
    synth_satcheck(new cancellable_solvert<satcheckt>()),
    synth_solver(new bv_pointerst(ns, *synth_satcheck)),
    synth_encoding(synth_encoding_factory()),
    program_size(1u),
    counterexample_counter(0u)
{
  set_message_handler(msg);
  init();
}

template <class satcheckt>
void incremental_prop_learnt<satcheckt>::init()
{
  synth_encoding->program_size = program_size;
  synth_satcheck->set_message_handler(get_message_handler());
  synth_solver->set_message_handler(get_message_handler());

  generate_constraint(
    ns, get_message_handler(), problem, counterexamples,
    *synth_encoding, *synth_solver);

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
  synth_encoding = synth_encoding_factory();
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
  return synth_encoding->get_expressions(*synth_solver);
}

template <class satcheckt>
void incremental_prop_learnt<satcheckt>::cancel()
{
  synth_satcheck->cancel();
}
