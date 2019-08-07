/*******************************************************************\

 Module: Fastsynth Language Frontend Utility

 Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

#ifndef CPROVER_FASTSYNTH_FRONTEND_UTIL_H
#define CPROVER_FASTSYNTH_FRONTEND_UTIL_H

#include <util/irep.h>

#include <chrono>
#include <set>

/// Searches for symbols that meet the criteria for being synthesised
/// expressions.
/// \param symbol_table: Symbol table to search through.
/// \param expression_prefix: Prefix of the expressions that should be
///   synthesised.
/// \return A set containing the name of each synthesised expression.
std::set<irep_idt> find_expressions(
  const class symbol_tablet &symbol_table,
  const std::string &expression_prefix);

/// Sets the verbosity of the output to the level that is desired by the user.
/// Sets it to default in the case that there is no value.
/// \param cmdline: Command line instance that may hold the verbosity property.
/// \param [out] mh: Message handler whose verbosity level shall be set.
void set_verbosity(
  const class cmdlinet &cmdline,
  class console_message_handlert &mh);

/// Prints the formula of the problem after the symex step. Used for debugging.
/// \param src: Formula that shall be displayed.
/// \param ns: Namespace to which the equation belongs.
/// \param mode: Language of the source. Defaults to ANSI-C.
void show_formula(
  const class symex_target_equationt &src,
  const class namespacet &ns,
  const irep_idt mode = irep_idt{});

/// Modifies all synthesised expressions inside of the given GOTO model so that
/// they can be distinguished from regular functions.
/// \param expressions: Set of synthesised expressions.
/// \param goto_model: GOTO model that shall be modified.
void instrument_expressions(
  const std::set<irep_idt> &expressions,
  class goto_modelt &goto_model);

/// Modifies all local variables inside of the given GOTO model so that
/// non-deterministic values are added to them right after their declarations.
/// \param expressions: Set of synthesised expressions.
/// \param goto_model: GOTO model that shall be modified.
void instrument_nondet_lokals(goto_modelt &goto_model);

/// Modifies the GOTO model in a way that it can be used for the synthesis.
/// \param goto_model: GOTO model that shall be modified.
void process_goto_model(goto_modelt &goto_model);

/// Configures the given CEGIS instance based on the command line arguments.
/// \param cmdline: Command line instance that may includes properties to set.
/// \param [out] cegis: CEGIS instance that shall be configured by this
///   function.
void set_cegis_cmdline_properties(const cmdlinet &cmdline, class cegist &cegis);

/// Prints all given expressions to the specified output.
/// \param [out] message: Object that shall receive the output.
/// \param expressions: Data structure that holds all expressions.
void print_expressions(
  class messaget &message,
  const std::set<irep_idt> &expressions);

/// Prints the result of the synthesis to the given output.
/// \param [out] message: Object that shall receive the output.
/// \param cegis: CEGIS instance that performed the synthesis and holds one or
///   more solution.
/// \param ns: Namespace, containing the symbols of the input and the symex
///   step.
/// \param mode: Language for which the synthesis was performed.
void print_synthesis_result(
  messaget &message,
  const cegist &cegis,
  const namespacet &ns,
  const irep_idt mode = irep_idt{});

/// Prints the duration of the synthesis to the given output.
/// \param [out] message: Object that shall receive the output.
/// \param synthesis_time: The duration of the synthesis process.
void print_synthesis_time(
  messaget &message,
  const std::chrono::duration<double> &synthesis_time);

#endif // CPROVER_FASTSYNTH_FRONTEND_UTIL_H
