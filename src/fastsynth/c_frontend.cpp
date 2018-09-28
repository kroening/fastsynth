#include <fastsynth/c_frontend.h>
#include <fastsynth/literals.h>

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <chrono>

#include <util/cmdline.h>
#include <util/cout_message.h>
#include <util/config.h>
#include <util/arith_tools.h>
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
            i.type=ASSIGN;
            function_application_exprt e(
              symbol_exprt(identifier, code_typet()),
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

void get_free_variables(
  const exprt &expr,
  std::set<exprt> &free_variables)
{
  for(const auto &op : expr.operands())
    get_free_variables(op, free_variables);

  if(expr.id()==ID_nondet_symbol)
  {
    // record
    free_variables.insert(expr);
  }
}

problemt generate_cegis_problem(
  const symex_target_equationt &src, const bool use_literals)
{
  problemt result;

  exprt::operandst assertions;

  for(const auto &step : src.SSA_steps)
  {
    if(step.is_assignment())
      result.side_conditions.push_back(step.cond_expr);
    else if(step.is_assume())
    {
      if(assertions.empty())
        result.side_conditions.push_back(step.cond_expr);
      else
        result.side_conditions.push_back(
          implies_exprt(conjunction(assertions), step.cond_expr));
    }
    else if(step.is_assert())
    {
      assertions.push_back(step.cond_expr);
      result.constraints.push_back(step.cond_expr);
    }
  }

  for(const auto &c : result.constraints)
    get_free_variables(c, result.free_variables);

  for(const auto &c : result.side_conditions)
    get_free_variables(c, result.free_variables);

  if(use_literals)
    result.literals=find_literals(result);

  return result;
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
    goto_model=initialize_goto_model(cmdline, mh);
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
  path_strategy_choosert path_strategy_chooser;
  auto path_storage=path_strategy_chooser.get("lifo");
  optionst options;
  goto_symext goto_symex(mh, goto_model.symbol_table, equation, options, *path_storage);

  goto_symex.symex_from_entry_point_of(
    goto_model.goto_functions,
    new_symbol_table);

  #if 0
  show_formula(equation, ns);
  #endif

  const bool use_literals=cmdline.isset("literals");
  const auto problem=generate_cegis_problem(equation, use_literals);

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
      message.result() << "Result: "
                       << f.first.get_identifier()
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
