#ifndef CPROVER_FASTSYNTH_LOCAL_SYNTH_ENCODING_H_
#define CPROVER_FASTSYNTH_LOCAL_SYNTH_ENCODING_H_

#include <fastsynth/synth_encoding.h>
#include <fastsynth/synth_encoding_factory.h>

/// Explores the neighbourhood of a given template solution.
class local_synth_encodingt : public synth_encodingt
{
  /// Template solution whose neighbourhood to explore.
  const std::map<symbol_exprt, exprt> &solution_template;

  /// Additional constraints to limit considered constants.
  const synth_encodingt::constraintst &constraints;

  /// Word type calcuated by synth_encodignt::e_datat.
  typet word_type;

public:
  /// Creates a `synth_encodingt` that uses the given solution as a template.
  /// \param solution_template local_synth_encodingt::solution_template
  /// \param constraints Additional constraints to limit considered constants.
  local_synth_encodingt(
    const std::map<symbol_exprt, exprt> &solution_template,
    const synth_encodingt::constraintst &constraints);

  /// \see synth_encodingt::operator()(const exprt &)
  exprt operator()(const exprt &) override;

  /// \see get_expressions(const decision_proceduret &)
  std::map<symbol_exprt, exprt>
  get_expressions(const decision_proceduret &) const override;
};

/// Creates a constant placeholder variable.
/// \param identifier Identifier of the synthesised function.
/// \param index Constant number.
/// \return Placeholder symbol for the described constant.
symbol_exprt
cval(const irep_idt &identifier, const size_t index, const typet &word_type);

/// Creates a factory for local neighbourhood search synth_encodingt instances.
/// \param solution local_synth_encodingt::solution_template
/// \param constraints local_synth_encodingt::constraints
/// \return Factory for encodings exploring the given solution's neighbourhood.
synth_encoding_factoryt local_synth_encoding(
  const std::map<symbol_exprt, exprt> &solution,
  const synth_encodingt::constraintst &constraints);

#endif /* CPROVER_FASTSYNTH_LOCAL_SYNTH_ENCODING_H_ */
