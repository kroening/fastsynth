#ifndef CPROVER_FASTSYNTH_VERIFY_ENCODING_BASE_H_
#define CPROVER_FASTSYNTH_VERIFY_ENCODING_BASE_H_

#include <fastsynth/cegis_types.h>

/// Implementing classes encode a test of a solution candidate against all
/// free inputs.
class verify_encoding_baset {
 public:
  /// Virtual default destructor for defined behaviour.
  virtual ~verify_encoding_baset() = default;

  /// Candidate solution type.
  using functionst = solutiont::functionst;

  /// Candidate solution to verify.
  functionst functions;

  /// Free input variables by which to test.
  std::set<exprt> free_variables;

  /// Encodes a verification constraint according to the configuration.
  /// \param constraint Constraint (sub-)expression to encode.
  /// \return Encoded verification expression.
  virtual exprt operator()(const exprt &constraint) const = 0;

  /// Extracts a counterexample input from an assignment in a
  /// decision_proceduret.
  /// \param solver decision_proceduret from which to extract the assignment.
  /// \return Expression assignments representing the counterexamle input.
  virtual counterexamplet get_counterexample(
      const class decision_proceduret &solver) const = 0;
};

#endif /* CPROVER_FASTSYNTH_VERIFY_ENCODING_BASE_H_ */
