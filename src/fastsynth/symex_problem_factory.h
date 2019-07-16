/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_FASTSYNTH_SYMEX_PROBLEM_FACTORY_H_
#define CPROVER_FASTSYNTH_SYMEX_PROBLEM_FACTORY_H_

/// Converts a previously symexed SSA equation to a CEGIS problem.
/// \param msg Message sink for SSA conversion tasks.
/// \param ns Namespace for prop_convt conversion from SSA to solver equation.
/// \param equation SSA equation to convert to CEGIS problem.
class problemt to_problem(
  class message_handlert &msg,
  const class namespacet &ns,
  class symex_target_equationt &equation);

/// Symexes and converts the given GOTO model to a CEGIS problem.
/// \param msg Message sink for all symbolic execution and SSA conversion tasks.
/// \param options Symbolic execution options.
/// \param new_symbol_table Symbol table that holds all new symbols after the
///   symex.
/// \param model GOTO model to convert.
/// \return CEGIS problem modelling the given GOTO program.
problemt to_problem(
  message_handlert &msg,
  const class optionst &options,
  class symbol_tablet &new_symbol_table,
  class abstract_goto_modelt &model);

#endif /* CPROVER_FASTSYNTH_SYMEX_PROBLEM_FACTORY_H_ */
