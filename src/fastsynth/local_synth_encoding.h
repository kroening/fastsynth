#ifndef CPROVER_FASTSYNTH_LOCAL_SYNTH_ENCODING_H_
#define CPROVER_FASTSYNTH_LOCAL_SYNTH_ENCODING_H_

#include <fastsynth/synth_encoding.h>

/// Explores the neighbourhood of a given template solution.
class local_synth_encodingt : public synth_encodingt
{
  /// Namespace to create zero expressions if applicable.
  const namespacet &ns;

  /// Template solution whose neighbourhood to explore.
  const solutiont &solution_template;

  /// Additional constraints to limit considered constants.
  const synth_encodingt::constraintst &extra_constraints;

  /// Word type calcuated by synth_encodignt::e_datat.
  typet word_type;

public:
  /// Creates a `synth_encodingt` that uses the given solution as a template.
  /// \param ns \see local_synth_encodingt::ns
  /// \param solution_template \see local_synth_encodingt::solution_template
  /// \param extra_constraints \see local_synth_encodingt::extra_constraints
  local_synth_encodingt(
    const namespacet &ns,
    const solutiont &solution_template,
    const synth_encodingt::constraintst &extra_constraints);

  /// \see synth_encodingt::operator()(const exprt &)
  exprt operator()(const exprt &) override;

  /// \see synth_encodingt::get_solution(const decision_proceduret &)
  solutiont get_solution(const decision_proceduret &) const override;
};

/// Creates a constant placeholder variable.
/// \param identifier Identifier of the synthesised function.
/// \param index Constant number.
/// \return Placeholder symbol for the described constant.
symbol_exprt
cval(const irep_idt &identifier, const size_t index, const typet &word_type);

#endif /* CPROVER_FASTSYNTH_LOCAL_SYNTH_ENCODING_H_ */
