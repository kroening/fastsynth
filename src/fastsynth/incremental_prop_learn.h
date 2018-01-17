#ifndef CPROVER_FASTSYNTH_INCREMENTAL_PROP_LEARN_H_
#define CPROVER_FASTSYNTH_INCREMENTAL_PROP_LEARN_H_

#include <fastsynth/learn.h>
#include <fastsynth/cegis.h>
#include <fastsynth/synth_encoding.h>

#include <solvers/sat/satcheck.h>

#include <memory>

/// Generates a constraint using synth_encodingt and solves it incrementally
/// using a configurable propt instance.
class incremental_prop_learnt : public learnt
{
  /// Message handler for decision procedure messages.
  messaget &msg;

  /// Namespace passed on to decision procedure.
  const namespacet &ns;

  /// Synthesis problem to solve.
  const cegist::problemt &problem;

  /// Solver instance.
  std::unique_ptr<satcheck_no_simplifiert> synth_satcheck;

  /// Decision procedure for synthesis logic.
  std::unique_ptr<class bv_pointerst> synth_solver;

  /// Synthesis learn constraint generator.
  synth_encodingt synth_encoding;

  /// \see learnt::set_program_size(size_t)
  size_t program_size;

  /// Number of counterexamples inserted.
  size_t counterexample_counter;

  /// Counterexample set to synthesise against.
  std::vector<verify_encodingt::counterexamplet> counterexamples;

  /// Initialises message handler and adds the base synthesis problem to the
  /// constraint.
  void init();

public:
  /// Creates an incremental learner.
  /// \param msg \see msg incremental_prop_learnt::msg
  /// \param ns \see ns incremental_prop_learnt::ns
  /// \param problem \see incremental_prop_learnt::problem
  incremental_prop_learnt(
    messaget &msg,
    const namespacet &ns,
    const cegist::problemt &problem);

  /// \see learnt::set_program_size(size_t)
  void set_program_size(size_t program_size) override;

  /// \see learnt::operator()()
  decision_proceduret::resultt operator()() override;

  /// \see learnt::get_expressions()
  std::map<symbol_exprt, exprt> get_expressions() const override;

  /// \see learnt::add(const verify_encodingt::counterexamplet &counterexample)
  void add(const verify_encodingt::counterexamplet &counterexample) override;
};

#endif /* CPROVER_FASTSYNTH_INCREMENTAL_PROP_LEARN_H_ */
