#ifndef CPROVER_FASTSYNTH_SYNTH_ENCODING_CONSTRAINTS_H_
#define CPROVER_FASTSYNTH_SYNTH_ENCODING_CONSTRAINTS_H_

#include <fastsynth/cegis.h>
#include <fastsynth/verify_encoding.h>

/// Adds an additional counterexample to the constraint.
/// \param ns Decision procedure namespace.
/// \param msg Message sink.
/// \param ce Counterexample to insert.
/// \param synth_encoding Synthesis encoding to extend by the counterexample.
/// \param prop_conv Solver instance.
void add_counterexample(
  const namespacet &ns,
  message_handlert &,
  const verify_encodingt::counterexamplet &ce,
  synth_encodingt &synth_encoding,
  prop_convt &prop_conv);

/// Inserts the base synthesis problem without counterexamples into the
/// constraint.
/// \param ns Decision procedure namespace.
/// \param msg Message sink.
/// \param problem Synthesis problem definition.
/// \param encoding Synthesis encoding to initialise with the base problem.
/// \param prop_conv Solver instance.
void add_problem(
  const namespacet &ns,
  message_handlert &,
  const cegist::problemt &problem,
  synth_encodingt &encoding,
  prop_convt &prop_conv);

/// Generates the full synthesis constraint. This entails adding each
/// counterexample with the given problem constraint.
/// \param ns Decision procedure namespace.
/// \param msg Message sink.
/// \param problem Synthesis problem definition.
/// \param ces Counterexample to insert.
/// \param synth_encoding Synthesis encoding to extend by the counterexample.
/// \param prop_conv Solver instance.
void generate_constraint(
  const namespacet &ns,
  message_handlert &,
  const cegist::problemt &problem,
  const std::vector<verify_encodingt::counterexamplet> &counterexamples,
  synth_encodingt &synth_encoding,
  prop_convt &prop_conv);

#endif /* CPROVER_FASTSYNTH_SYNTH_ENCODING_CONSTRAINTS_H_ */
