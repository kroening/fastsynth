#ifndef CPROVER_FASTSYNTH_LOCAL_SEARCH_H_
#define CPROVER_FASTSYNTH_LOCAL_SEARCH_H_

#include <fastsynth/learn.h>

///
class local_learnt: public learnt
{
  learnt &learn;
public:
  ///
  /// \param learn
  explicit local_learnt(learnt &learn);

  /// \see learnt::set_program_size(size_t)
  void set_program_size(size_t program_size) override;

  /// \see learnt::operator()()
  decision_proceduret::resultt operator()() override;

  /// \see learnt::get_expressions()
  std::map<symbol_exprt, exprt> get_expressions() const override;

  /// \see learnt::add(const verify_encodingt::counterexamplet &counterexample)
  void add(const verify_encodingt::counterexamplet &counterexample) override;
};

#endif /* CPROVER_FASTSYNTH_LOCAL_SEARCH_H_ */
