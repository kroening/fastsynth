#ifndef CPROVER_FASTSYNTH_SYNTH_ENCODING_BASE_H_
#define CPROVER_FASTSYNTH_SYNTH_ENCODING_BASE_H_

#include <fastsynth/cegis_types.h>

/// Implementing classes encode a choice of valid programs to synthesise.
class synth_encoding_baset {
 public:
  /// Default synthesis configuration.
  synth_encoding_baset()
      : program_size(1u), enable_division(false), enable_bitwise(false) {}

  /// Virtual default destructor for defined behaviour.
  virtual ~synth_encoding_baset() = default;

  /// Encodes a synthesis constraint according to the synthesis configuration.
  /// \param expr Constraint (sub-)expression to encode.
  /// \return Encoded synthesis expression.
  virtual exprt operator()(const exprt &expr) = 0;

  /// Extracts a candidate program from an assignment in a decision_proceduret.
  /// \param solver decision_proceduret from which to extract the assignment.
  /// \return Expression assignments representing the candidate solution.
  virtual solutiont get_solution(
      const class decision_proceduret &solver) const = 0;

  /// Clears any stored constraints, but leaves the configuration intact.
  virtual void clear() = 0;

  /// Counterexample suffix to append to symbols.
  std::string suffix;

  /// Maximum size of the synthesised programs.
  std::size_t program_size;

  /// Indicates whether division is allowed in synthesised programs.
  bool enable_division;

  /// Indicates whether bitwise operations are allowed in synthesised programs.
  bool enable_bitwise;

  /// Mutable list of constraints.
  using constraintst = std::list<exprt>;

  /// Holds additional constraints generated during instrumentation.
  constraintst constraints;

  /// Pre-configured constants to include in the expression set.
  std::set<constant_exprt> literals;
};

#endif /* CPROVER_FASTSYNTH_SYNTH_ENCODING_BASE_H_ */
