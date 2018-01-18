/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <fastsynth/composite_learn.h>

#include <util/namespace.h>
#include <util/irep_serialization.h>

#include <algorithm>
#include <thread>

void composite_learnt::set_program_size(const size_t program_size)
{
  for(const std::unique_ptr<learnt> &learn : learners)
  {
    learn->cancel();
    learn->set_program_size(program_size);
  }
}

namespace
{
/// Helper class tracking the status of a learn thread.
class workert
{
  /// Reference to all learners in the composite. Used to cancel other threads
  /// on success.
  const std::vector<std::unique_ptr<learnt>> &learners;

public:
  /// This worker's learner instance.
  learnt &learn;

  /// Result of this worker's query.
  decision_proceduret::resultt result;

  /// Creates a new learner worker thread.
  /// \param learners \see workert::learners
  /// \param learn \see workert::learn
  workert(
    const std::vector<std::unique_ptr<learnt>> &learners,
    learnt &learn)
    : learners(learners),
      learn(learn),
      result(decision_proceduret::resultt::D_ERROR)
  {
  }

  /// Executes the associated learner and cancels other learners on success.
  void operator()()
  {
    result = learn();
    if(is_sat())
      for_each(begin(learners), end(learners), std::mem_fn(&learnt::cancel));
  }

  /// Indicates whether this learner received a SAT result.
  bool is_sat() const
  {
    return decision_proceduret::resultt::D_SATISFIABLE == result;
  }

  /// Indicates whether this learner received an UNSAT result.
  bool is_unsat() const
  {
    return decision_proceduret::resultt::D_UNSATISFIABLE == result;
  }
};
}

decision_proceduret::resultt composite_learnt::operator()()
{
  std::vector<workert> workers;
  transform(
    begin(learners),
    end(learners),
    back_inserter(workers),
    [this](const std::unique_ptr<learnt> &learn)
      { return workert(learners, *learn); });

  std::vector<std::thread> threads(workers.size());
  transform(
    begin(workers),
    end(workers),
    begin(threads),
    [](workert &worker) { return std::thread(std::ref(worker)); });

  for_each(begin(threads), end(threads), std::mem_fn(&std::thread::join));

  const std::vector<workert>::const_iterator first_satisfiable =
    find_if(begin(workers), end(workers), std::mem_fn(&workert::is_sat));
  if(end(workers) != first_satisfiable)
  {
    first_solution = first_satisfiable->learn.get_expressions();
    return decision_proceduret::resultt::D_SATISFIABLE;
  }

  if(any_of(begin(workers), end(workers), std::mem_fn(&workert::is_unsat)))
    return decision_proceduret::resultt::D_UNSATISFIABLE;

  return decision_proceduret::resultt::D_ERROR;
}

std::map<symbol_exprt, exprt> composite_learnt::get_expressions() const
{
  return first_solution;
}

void composite_learnt::add(
  const verify_encodingt::counterexamplet &counterexample)
{
  for(const std::unique_ptr<learnt> &learn : learners)
    learn->add(counterexample);
}

void composite_learnt::cancel()
{
  for_each(begin(learners), end(learners), std::mem_fn(&learnt::cancel));
}
