#ifndef CPROVER_FASTSYNTH_CONSTANT_LIMITS_H_
#define CPROVER_FASTSYNTH_CONSTANT_LIMITS_H_

#include <fastsynth/synth_encoding.h>

#include <util/message.h>

/// Employs an SMT solver to quickly test whether a solution using constants
/// above or below certain values are feasible.
class constant_limitst : public messaget
{
  /// Namespace passed to underlying solver.
  const namespacet &ns;

  /// CEGIS problem to solve.
  const class problemt &problem;

  /// Solution template used to construct local encodings.
  const solutiont &solution_template;

  /// Performs a limited synthesis SMT query.
  /// \param additional_constraints Additional constraints. Usually restricts
  ///   local search to only certain constants.
  /// \return Query result.
  decision_proceduret::resultt
  decide(const synth_encodingt::constraintst &additional_constraints);

public:
  /// Result container for learned constraints. These are considered by the
  /// CEGIS loop in `local_cegist`.
  synth_encodingt::constraintst result_constraints;

  /// On the off chance that SMT actually just finds a solution.
  solutiont solution;

  /// Constructs and automatically starts a constant_limitst dispatch handler.
  /// \param msg Message sink to use for progress messages.
  /// \param ns \see constant_limitst::ns
  /// \param problem \see constant_limitst::problem
  /// \param solution_template \see constant_limitst::solution_template
  constant_limitst(
    message_handlert &msg,
    const namespacet &ns,
    const problemt &problem,
    const solutiont &solution_template);

  /// Runs an SMT limits analysis on the given candidate.
  /// \param candidate New candidate whose constants to explore.
  /// \return Indicates whether a solution or constraint was found.
  decision_proceduret::resultt operator()(const solutiont &candiate);
};

#endif /* CPROVER_FASTSYNTH_CONSTANT_LIMITS_H_ */
