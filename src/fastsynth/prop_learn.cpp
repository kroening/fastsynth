#include <fastsynth/prop_learn.h>
#include <fastsynth/synth_encoding.h>
#include <fastsynth/synth_encoding_constraints.h>

#include <solvers/flattening/bv_pointers.h>

#include <minisat/simp/SimpSolver.h>

#include <mutex>

prop_learnt::prop_learnt(
  message_handlert &msg,
  const namespacet &ns,
  const cegist::problemt &problem,
  const synth_encoding_factoryt synth_encoding_factory)
  : ns(ns),
    problem(problem),
    synth_encoding_factory(synth_encoding_factory),
    program_size(1u)
{
  set_message_handler(msg);
}

void prop_learnt::set_program_size(const size_t program_size)
{
  this->program_size = program_size;
}

/// Makes irept operations in prop_learnt::operator()() thread-safe. This
/// assumes that no other threads other than prop_learnt::operator()()
/// invocations perform irept operations.
static std::mutex IREP_MUTEX;

decision_proceduret::resultt prop_learnt::operator()()
{
  std::unique_lock<std::mutex> lock(IREP_MUTEX);
  const std::shared_ptr<cancellable_solvert<satcheckt>> synth_satcheck(
    std::make_shared<cancellable_solvert<satcheckt>>());
  this->synth_satcheck = synth_satcheck;

  synth_satcheck->set_message_handler(get_message_handler());

  bv_pointerst synth_solver(ns, *synth_satcheck);
  synth_solver.set_message_handler(get_message_handler());

  const std::unique_ptr<synth_encodingt> synth_enc(synth_encoding_factory());
  synth_enc->program_size = program_size;

  generate_constraint(
    ns, get_message_handler(), problem, counterexamples,
    *synth_enc, synth_solver);

  lock.unlock();
  const decision_proceduret::resultt result(synth_solver());
  lock.lock();

  if(decision_proceduret::resultt::D_SATISFIABLE == result)
    last_solution = synth_enc->get_expressions(synth_solver);

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

void prop_learnt::cancel()
{
  const std::shared_ptr<cancellable_solvert<satcheckt>> solver(
    synth_satcheck.lock());
  if(solver)
    solver->cancel();
}
