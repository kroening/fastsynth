#ifndef CPROVER_FASTSYNTH_PROP_LEARN_H_
#define CPROVER_FASTSYNTH_PROP_LEARN_H_

#include <fastsynth/learn.h>
#include <fastsynth/cegis.h>

class solver_learn_baset:public learnt
{
protected:
  /// Namespace passed on to decision procedure.
  const namespacet &ns;

  /// Synthesis problem to solve.
  const cegist::problemt &problem;

  /// Addds an additional counterexample to the constraint.
  /// \param ce Counterexample to insert.
  /// \param synth_encoding Synthesis encoding to extend by the counterexample.
  /// \param solver Solver instance.
  void add_counterexample(
    const verify_encodingt::counterexamplet &,
    synth_encodingt &,
    decision_proceduret &);

  /// Inserts the base synthesis problem without counterexamples into the
  /// constraint.
  /// \param encoding Synthesis encoding to initialise with the base problem.
  /// \param solver Solver instance.
  void add_problem(synth_encodingt &, decision_proceduret &);

  /// Creates the base class.
  /// \param ns \see ns solver_learnt::ns
  /// \param problem \see solver_learnt::problem
  /// \param msg \see msg solver_learnt::msg
  solver_learn_baset(
    const namespacet &,
    const cegist::problemt &,
    message_handlert &);
};

/// Default learner implementation. Generates a constraint using synth_encodingt
/// and solves it using a configurable propt instance.
class solver_learnt:public solver_learn_baset
{
  /// \see learnt::set_program_size(size_t)
  size_t program_size;

  /// Counterexample set to synthesise against.
  std::vector<verify_encodingt::counterexamplet> counterexamples;

  /// Solution created in the last invocation of solver_learnt::operator()().
  std::map<symbol_exprt, exprt> last_solution;

public:
  /// Creates a non-incremental learner.
  /// \param msg \see msg solver_learnt::msg
  /// \param ns \see ns solver_learnt::ns
  /// \param problem \see solver_learnt::problem
  solver_learnt(
    const namespacet &,
    const cegist::problemt &,
    message_handlert &);

  /// Enable Fourier-Motzkin
  bool use_fm;

  /// \see learnt::set_program_size(size_t)
  void set_program_size(size_t program_size) override;

  /// \see learnt::operator()()
  decision_proceduret::resultt operator()() override;

  /// \see learnt::get_expressions()
  std::map<symbol_exprt, exprt> get_expressions() const override;

  /// \see learnt::add(const verify_encodingt::counterexamplet &counterexample)
  void add(const verify_encodingt::counterexamplet &) override;
};

#endif /* CPROVER_FASTSYNTH_PROP_LEARN_H_ */
