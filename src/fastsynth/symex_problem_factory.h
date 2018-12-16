/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_FASTSYNTH_SYMEX_PROBLEM_FACTORY_H_
#define CPROVER_FASTSYNTH_SYMEX_PROBLEM_FACTORY_H_

/// Symexes and converts the given GOTO model to a CEGIS problem.
/// \param msg Message sink for all symbolic execution and SSA conversion tasks.
/// \param options Symbolic execution options.
/// \param model GOTO model to convert.
/// \return CEGIS problem modelling the given GOTO program.
class problemt to_problem(
  class message_handlert &msg,
  const class optionst &options,
  class abstract_goto_modelt &model);

#endif /* CPROVER_FASTSYNTH_SYMEX_PROBLEM_FACTORY_H_ */
