#include <fastsynth/c_frontend.h>
#include <fastsynth/literals.h>
#include <fastsynth/symex_problem_factory.h>

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <chrono>

#include <util/cmdline.h>
#include <util/cout_message.h>
#include <util/config.h>
#include <util/arith_tools.h>
#include <util/expr_iterator.h>
#include <util/mathematical_types.h>
#include <util/prefix.h>
#include <util/std_types.h>

#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/goto_convert_functions.h>

#include <goto-symex/goto_symex.h>
#include <goto-symex/symex_target_equation.h>

#include <ansi-c/ansi_c_language.h>

#include <langapi/mode.h>
#include <langapi/language_util.h>

#include <solvers/flattening/bv_pointers.h>

#include "cegis.h"

std::set<irep_idt> find_expressions(const goto_modelt &goto_model)
{
  std::set<irep_idt> result;

  for(auto &s : goto_model.symbol_table.symbols)
  {
    if(!s.second.is_state_var &&
       s.second.type.id()==ID_code &&
       s.second.value.is_nil() &&
       has_prefix(id2string(s.first), "EXPRESSION"))
      result.insert(s.first);
  }

  return result;
}

void instrument_expressions(
  const std::set<irep_idt> &expressions,
  goto_modelt &goto_model)
{
  for(auto &f : goto_model.goto_functions.function_map)
    for(auto &i : f.second.body.instructions)
    {
      if(i.is_function_call())
      {
        auto &c=to_code_function_call(i.code);
        if(c.function().id()==ID_symbol)
        {
          irep_idt identifier=to_symbol_expr(c.function()).get_identifier();
          if(expressions.find(identifier)!=expressions.end() &&
             c.lhs().is_not_nil())
          {
            const code_typet &code_type = to_code_type(c.function().type());
            const typet &codomain = code_type.return_type();
            const code_typet::parameterst &params = code_type.parameters();
            mathematical_function_typet::domaint domain(params.size());

            transform(
              begin(params),
              end(params),
              begin(domain),
              [](const code_typet::parametert &param) { return param.type(); });

            const mathematical_function_typet type(domain, codomain);

            i.type=ASSIGN;

            function_application_exprt e(
              symbol_exprt(identifier, type),
              c.arguments(),
              c.lhs().type());

            i.code=code_assignt(c.lhs(), e);
          }
        }
      }
    }
}

void show_formula(
  const symex_target_equationt &src,
  const namespacet &ns)
{
  for(const auto &step : src.SSA_steps)
  {
    if(step.is_assignment() ||
       step.is_assume())
    {
      std::cout << "P: " << from_expr(ns, "", step.cond_expr) << '\n';
    }
    else if(step.is_assert())
    {
      std::cout << "A: " << from_expr(ns, "", step.cond_expr) << '\n';
    }
  }
}

int c_frontend(const cmdlinet &cmdline)
{
  console_message_handlert mh;
  messaget message(mh);

  // this is our default verbosity
  unsigned int v=messaget::M_STATISTICS;

  if(cmdline.isset("verbosity"))
  {
    v=std::stol(
        cmdline.get_value("verbosity"));;
    if(v>10)
      v=10;
  }

  mh.set_verbosity(v);

  register_language(new_ansi_c_language);

  config.set(cmdline);
  config.ansi_c.set_arch_spec_i386();

  PRECONDITION(cmdline.args.size()==1);

  goto_modelt goto_model;

  try
  {
    optionst options;
    goto_model=initialize_goto_model(cmdline.args, mh, options);
  }
  catch(...)
  {
    return 1;
  }

  auto expressions=find_expressions(goto_model);

  for(const auto &i : expressions)
    message.status() << "EXPRESSION: " << i << messaget::eom;

  instrument_expressions(expressions, goto_model);

  symbol_tablet new_symbol_table;
  namespacet ns(goto_model.symbol_table, new_symbol_table);
  symex_target_equationt equation;
  auto path_storage=get_path_strategy("lifo");
  optionst options;

  goto_symext goto_symex(mh, goto_model.symbol_table, equation, options, *path_storage);

  auto get_goto_function = [&goto_model](const irep_idt &id) ->
    const goto_functionst::goto_functiont &
    {
      return goto_model.get_goto_function(id);
    };

  goto_symex.symex_from_entry_point_of(
    get_goto_function,
    new_symbol_table);

  #if 0
  show_formula(equation, ns);
  #endif

  problemt problem = to_problem(mh, options, goto_model);
  if(cmdline.isset("literals"))
    add_literals(problem);

  cegist cegis(ns);
  cegis.set_message_handler(mh);

  if(cmdline.isset("max-program-size"))
    cegis.max_program_size=std::stol(
      cmdline.get_value("max-program-size"));
  else
    cegis.max_program_size=5; // default

  cegis.incremental_solving=cmdline.isset("incremental");
  cegis.use_simp_solver=cmdline.isset("simplifying-solver");
  cegis.use_fm=cmdline.isset("fm");
  cegis.enable_bitwise=!cmdline.isset("no-bitwise");\
  cegis.use_smt=cmdline.isset("smt");
  cegis.enable_division=cmdline.isset("enable-division");
  cegis.logic="BV"; //default logic

  auto start_time=std::chrono::steady_clock::now();

  switch(cegis(problem))
  {
  case decision_proceduret::resultt::D_SATISFIABLE:

    for(const auto &f : cegis.solution.functions)
    {
      const exprt &name = to_ssa_expr(f.first).get_original_expr();
      message.result() << "Result: "
                       << to_symbol_expr(name).get_identifier()
                       << " -> "
                       << from_expr(ns, "", f.second)
                       << '\n';
    }

    message.result() << messaget::eom;

    message.statistics() << "Synthesis time: "
                         << std::chrono::duration<double>(
                              std::chrono::steady_clock::now()-start_time).count()
                         << 's'
                         << messaget::eom;
    break;

  default:
    return 1;
  }

  return 0;
}
