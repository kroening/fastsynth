#include <fastsynth/prop_learn.h>
#include <fastsynth/synth_encoding.h>

#include <solvers/flattening/bv_pointers.h>

#include <langapi/language_util.h>

#include <minisat/simp/SimpSolver.h>

#include <mutex>

prop_learnt::prop_learnt(
  messaget &msg,
  const namespacet &ns,
  const cegist::problemt &problem)
  : msg(msg), ns(ns), problem(problem), program_size(1u)
{
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

  synth_satcheck->set_message_handler(msg.get_message_handler());

  bv_pointerst synth_solver(ns, *synth_satcheck);
  synth_solver.set_message_handler(msg.get_message_handler());

  synth_encodingt synth_encoding;
  synth_encoding.program_size = program_size;

  if(counterexamples.empty())
  {
    synth_encoding.suffix = "$ce";
    synth_encoding.constraints.clear();

    add_problem(ns, msg, problem, synth_encoding, synth_solver);
  }
  else
  {
    std::size_t counter = 0;
    for(const auto &c : counterexamples)
    {
      synth_encoding.suffix = "$ce" + std::to_string(counter);
      synth_encoding.constraints.clear();
      add_counterexample(ns, msg, c, synth_encoding, synth_solver);

      add_problem(ns, msg, problem, synth_encoding, synth_solver);

      counter++;
    }
  }

  lock.unlock();
  const decision_proceduret::resultt result(synth_solver());
  lock.lock();

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

void prop_learnt::cancel()
{
  const std::shared_ptr<cancellable_solvert<satcheckt>> solver(
    synth_satcheck.lock());
  if(solver)
    solver->cancel();
}

void add_counterexample(
  const namespacet &ns,
  messaget &msg,
  const verify_encodingt::counterexamplet &ce,
  synth_encodingt &synth_encoding,
  prop_convt &prop_conv)
{
  for(const auto &it : ce)
  {
    const exprt &symbol = it.first;
    const exprt &value = it.second;

    exprt encoded = synth_encoding(equal_exprt(symbol, value));
    msg.debug() << "ce: " << from_expr(ns, "", encoded) << messaget::eom;
    prop_conv.set_to_true(encoded);
  }
}

void add_problem(
  const namespacet &ns,
  messaget &msg,
  const cegist::problemt &problem,
  synth_encodingt &encoding,
  prop_convt &prop_conv)
{
  for(const exprt &e : problem.side_conditions)
  {
    const exprt encoded = encoding(e);
    msg.debug() << "sc: " << from_expr(ns, "", encoded) << messaget::eom;
    prop_conv.set_to_true(encoded);
  }

  for(const auto &e : problem.constraints)
  {
    const exprt encoded = encoding(e);
    msg.debug() << "co: " << from_expr(ns, "", encoded) << messaget::eom;
    prop_conv.set_to_true(encoded);
  }

  for(const auto &c : encoding.constraints)
  {
    prop_conv.set_to_true(c);
    msg.debug() << "ec: " << from_expr(ns, "", c) << messaget::eom;
  }
}
