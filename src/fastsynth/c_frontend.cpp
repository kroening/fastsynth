#include <iostream>
#include <fstream>
#include <cstdlib>

#include <util/cmdline.h>
#include <util/cout_message.h>
#include <util/config.h>
#include <util/arith_tools.h>
#include <util/std_types.h>
#include <util/time_stopping.h>

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
            function_application_exprt e(c.lhs().type());
            e.arguments()=c.arguments();
            e.function()=symbol_exprt(identifier, code_typet());
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

cegist::problemt generate_cegis_problem(
  const symex_target_equationt &src)
{
  cegist::problemt result;

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

  return result;
}

int c_frontend(const cmdlinet &cmdline)
{
  console_message_handlert mh;
  messaget message(mh);

  register_language(new_ansi_c_language);

  config.set(cmdline);
  config.ansi_c.set_arch_spec_i386();
  
  assert(cmdline.args.size()==1);

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
  symex_target_equationt equation(ns);
  goto_symext goto_symex(mh, ns, new_symbol_table, equation);
  
  goto_symex(goto_model.goto_functions);

  #if 0
  show_formula(equation, ns);
  #endif
  
  const auto problem=generate_cegis_problem(equation);

  cegist cegis(ns);
  cegis.set_message_handler(mh);
  
  if(cmdline.isset("max-program-size"))
    cegis.max_program_size=std::stol(
      cmdline.get_value("max-program-size"));
  else
    cegis.max_program_size=5; // default

  cegis.incremental_solving=cmdline.isset("incremental");
  cegis.incremental_solving=cmdline.isset("simplifying-solver");


  auto start_time=current_time();

  switch(cegis(problem))
  {
  case decision_proceduret::resultt::D_SATISFIABLE:

    for(const auto &e : cegis.expressions)
    {
      message.result() << "Result: "
                       << e.first.get_identifier()
                       << " -> "
                       << from_expr(ns, "", e.second)
                       << '\n';
    }

    message.result() << messaget::eom;
    
    message.statistics() << "Synthesis time: "
                         << current_time()-start_time
                         << 's'
                         << messaget::eom;
    break;

  default:
    return 1;
  }

  return 0;
}
