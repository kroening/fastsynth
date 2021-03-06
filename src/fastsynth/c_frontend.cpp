/*******************************************************************\

 Module: Fastsynth ANSI-C Language Frontend

 Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "c_frontend.h"
#include "cegis.h"
#include "frontend_util.h"
#include "literals.h"
#include "symex_problem_factory.h"
#include "synth_encoding.h"
#include "verify_encoding.h"

#include <ansi-c/ansi_c_language.h>

#include <langapi/mode.h>

#include <goto-programs/initialize_goto_model.h>

#include <util/cmdline.h>
#include <util/config.h>
#include <util/cout_message.h>
#include <util/expr_iterator.h>
#include <util/options.h>

#include <chrono>

/// Prefix that precedes each synthesised expression in C.
#define C_EXPRESSION_PREFIX "EXPRESSION"

int c_frontend(const cmdlinet &cmdline)
{
  // Environment setup.
  console_message_handlert mh;
  messaget message(mh);
  set_verbosity(cmdline, mh);
  register_language(new_ansi_c_language);
  config.set(cmdline);
  config.ansi_c.set_arch_spec_i386();

  // Initialise GOTO model.
  PRECONDITION(cmdline.args.size() == 1);
  goto_modelt goto_model;

  try
  {
    optionst options;
    goto_model = initialize_goto_model(cmdline.args, mh, options);
  }
  catch(...)
  {
    return 1;
  }

  // Modify GOTO model for synthesis.
  std::set<irep_idt> expressions =
    find_expressions(goto_model.symbol_table, C_EXPRESSION_PREFIX);
  print_expressions(message, expressions);
  instrument_expressions(expressions, goto_model);
  process_goto_model(goto_model);

  // Perform symex to get a mathematical representation of the problem.
  optionst options;
  options.set_option("propagation", true);
  options.set_option("simplify", true);
  symbol_tablet symex_symbol_table;
  problemt problem{to_problem(mh, options, symex_symbol_table, goto_model)};
  if(cmdline.isset("literals"))
    add_literals(problem);

  // Use symbol tables for creating a namespace and CEGIS instance.
  namespacet ns(goto_model.symbol_table, symex_symbol_table);
  synth_encodingt synth_encoding;
  verify_encodingt verify_encoding;
  cegist cegis(ns);
  cegis.set_message_handler(mh);
  set_cegis_cmdline_properties(cmdline, cegis);

  // Perform synthesis and measure the time.
  std::chrono::steady_clock::time_point start_time{
    std::chrono::steady_clock::now()};
  decision_proceduret::resultt result{
    cegis(problem, synth_encoding, verify_encoding)};
  std::chrono::duration<double> synthesis_time{
    std::chrono::steady_clock::now() - start_time};

  if(decision_proceduret::resultt::D_SATISFIABLE == result)
  {
    print_synthesis_result(message, cegis, ns);
    print_synthesis_time(message, synthesis_time);
    return 0;
  }
  else
    return 1;
}
