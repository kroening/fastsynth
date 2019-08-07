/*******************************************************************\

 Module: Fastsynth Statement List Language Frontend

 Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

#include "statement_list_frontend.h"
#include "bool_synth_encoding.h"
#include "cegis.h"
#include "frontend_util.h"
#include "literals.h"
#include "symex_problem_factory.h"
#include "verify_encoding.h"

#include <statement-list/statement_list_language.h>
#include <statement-list/statement_list_typecheck.h>

#include <langapi/mode.h>

#include <goto-programs/initialize_goto_model.h>

#include <util/cmdline.h>
#include <util/config.h>
#include <util/cout_message.h>
#include <util/expr_iterator.h>
#include <util/options.h>

#include <chrono>

/// Prefix that precedes each synthesised expression in STL.
#define STL_EXPRESSION_PREFIX "EXPRESSION"

int statement_list_frontend(const cmdlinet &cmdline)
{
  // Environment setup.
  console_message_handlert mh;
  messaget message(mh);
  set_verbosity(cmdline, mh);
  register_language(new_statement_list_language);
  config.set(cmdline);
  config.ansi_c.set_arch_spec_x86_64();

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
    find_expressions(goto_model.symbol_table, STL_EXPRESSION_PREFIX);
  print_expressions(message, expressions);
  instrument_nondet_lokals(goto_model);
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
  cegist cegis(ns);
  cegis.set_message_handler(mh);
  set_cegis_cmdline_properties(cmdline, cegis);

  // Perform synthesis and measure the time.
  bool_synth_encodingt bool_synth_encoding;
  verify_encodingt verify_encoding;
  std::chrono::steady_clock::time_point start_time{
    std::chrono::steady_clock::now()};
  decision_proceduret::resultt result{
    cegis(problem, bool_synth_encoding, verify_encoding)};
  std::chrono::duration<double> synthesis_time{
    std::chrono::steady_clock::now() - start_time};

  if(decision_proceduret::resultt::D_SATISFIABLE == result)
  {
    print_synthesis_result(message, cegis, ns, ID_statement_list);
    print_synthesis_time(message, synthesis_time);
    return 0;
  }
  else
    return 1;
}
