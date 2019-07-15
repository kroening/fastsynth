#ifndef CPROVER_FASTSYNTH_INCREMENTAL_PROP_LEARN_H_
#define CPROVER_FASTSYNTH_INCREMENTAL_PROP_LEARN_H_

#include <fastsynth/learn.h>
#include <fastsynth/cegis.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include <memory>

#include "solver_learn.h"

/// Generates a constraint using synth_encodingt and solves it incrementally
/// using a configurable propt instance.
class incremental_solver_learnt:public solver_learn_baset
{
  /// Solver instance.
  std::unique_ptr<propt> synth_satcheck;

  /// Decision procedure for synthesis logic.
  std::unique_ptr<class bv_pointerst> synth_solver;

  /// \see learnt::set_program_size(size_t)
  size_t program_size;

  /// Number of counterexamples inserted.
  size_t counterexample_counter;

  /// Counterexample set to synthesise against.
  std::vector<counterexamplet> counterexamples;

  /// Boolean indicates whether to use simplifying solver
  bool use_simp_solver;

  /// Initialises message handler and adds the base synthesis problem to the
  /// constraint.
  void init();

public:
  /// Creates an incremental learner.
  /// \param msg \see msg incremental_solver_learnt::msg
  /// \param ns \see ns incremental_solver_learnt::ns
  /// \param problem \see incremental_solver_learnt::problem
  /// \param synth_encoding \see solver_learn_baset::synth_encoding
  /// \param use_simp_solver indicates whether to use simplifying solver
  incremental_solver_learnt(
    const namespacet &,
    const problemt &,
    synth_encoding_baset &synth_encoding,
    bool use_simp_solver,
    message_handlert &);

  /// \see learnt::set_program_size(size_t)
  void set_program_size(size_t program_size) override;

  /// \see learnt::operator()()
  decision_proceduret::resultt operator()() override;

  /// \see learnt::get_expressions()
  solutiont get_solution() const override;

  /// \see learnt::add(const verify_encodingt::counterexamplet &counterexample)
  void add_ce(const counterexamplet &) override;

  /// \brief freezes variables in the sat solver associated to the
  /// expression to be synthesised. Needed when the incremental solver with
  /// simplifier is used
  void freeze_expression_symbols();
};

#endif /* CPROVER_FASTSYNTH_INCREMENTAL_PROP_LEARN_H_ */
