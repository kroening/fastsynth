#ifndef CPROVER_FASTSYNTH_COMPOSITE_LEARN_H_
#define CPROVER_FASTSYNTH_COMPOSITE_LEARN_H_

#include <fastsynth/learn.h>

#include <memory>

/// Thread pool implementation for learnt.
class composite_learnt : public learnt
{
  /// All parallel learners.
  std::vector<std::unique_ptr<learnt>> learners;

  /// First solution by any of the learners.
  std::map<symbol_exprt, exprt> first_solution;

public:
  /// \see learnt::set_program_size(size_t)
  void set_program_size(size_t program_size) override;

  /// \see learnt::operator()()
  decision_proceduret::resultt operator()() override;

  /// \see learnt::get_expressions()
  std::map<symbol_exprt, exprt> get_expressions() const override;

  /// \see learnt::add(const verify_encodingt::counterexamplet &counterexample)
  void add(const verify_encodingt::counterexamplet &counterexample) override;

  /// \see learnt::cancel()
  void cancel() override;

  /// \see messaget::set_message_handler(message_handlert &)
  void set_message_handler(message_handlert &_message_handler) override;

  /// Adds a new learner to the composite.
  /// \tparam T Type of the learner.
  /// \tparam argst Types of the learner's constructor arguments.
  /// \param args New learner's constructor arguments.
  template <class T, class... argst>
  void add(argst &... args)
  {
    learners.emplace_back(std::unique_ptr<learnt>(new T(args...)));
  }
};

#endif /* CPROVER_FASTSYNTH_COMPOSITE_LEARN_H_ */
