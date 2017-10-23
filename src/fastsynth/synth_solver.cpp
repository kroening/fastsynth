#include "synth_solver.h"

#include <langapi/language_util.h>

exprt synth_solvert::e_datat::instructiont::result(
  const std::vector<exprt> &arguments)
{
  if(parameter_sel.empty())
    return constant_val;

  exprt result_expr=constant_val;
  exprt selector=constant_sel;

  assert(arguments.size()==parameter_sel.size());

  for(std::size_t i=0; i<parameter_sel.size(); i++)
  {
    result_expr=if_exprt(selector, result_expr, arguments[i]);
    selector=parameter_sel[i];
  }

  return result_expr;
}

void synth_solvert::e_datat::setup(
  const function_application_exprt &e)
{
  if(setup_done) return;
  setup_done=true;

  function_symbol=e.function();
  const irep_idt &identifier=function_symbol.get_identifier();

  instructions.reserve(1);

  for(std::size_t pc=0; pc<1; pc++)
  {
    instructions.push_back(instructiont(pc));
    auto &instruction=instructions[pc];

    // constant
    irep_idt const_sel_id=id2string(identifier)+"_"+std::to_string(pc)+"_csel";
    irep_idt const_val_id=id2string(identifier)+"_"+std::to_string(pc)+"_cval";
    instruction.constant_sel=symbol_exprt(const_sel_id, bool_typet());
    instruction.constant_val=symbol_exprt(const_val_id, e.type());

    // one of the arguments
    const auto &arguments=e.arguments();
    instruction.parameter_sel.resize(arguments.size());

    for(std::size_t i=0; i<arguments.size(); i++)
    {
      irep_idt param_sel_id=id2string(identifier)+"_"+
               std::to_string(pc)+"_p"+std::to_string(i)+"sel";
      instruction.parameter_sel[i]=symbol_exprt(param_sel_id, bool_typet());
    }
  }
}

exprt synth_solvert::e_datat::result(
  const std::vector<exprt> &arguments)
{
  std::vector<exprt> results;
  results.resize(instructions.size());

  for(std::size_t pc=0; pc<instructions.size(); pc++)
    results[pc]=instructions[pc].result(arguments);

  assert(!results.empty());

  return results.back();
}

bvt synth_solvert::convert_bitvector(const exprt &expr)
{
  if(expr.id()==ID_function_application)
  {
    const auto &e=to_function_application_expr(expr);

    e_datat &e_data=e_data_map[e.function()];
    e_data.setup(e);

    exprt final_result=e_data.result(e.arguments());
    
    status() << "Application: " << from_expr(ns, "", final_result) << eom;

    return BASEt::convert_bitvector(final_result);
  }
  else
    return BASEt::convert_bitvector(expr);
}

std::map<symbol_exprt, exprt> synth_solvert::get_expressions() const
{
  std::map<symbol_exprt, exprt> result;

  for(const auto &e : e_data_map)
    result[e.first]=get_expression(e.second);

  return result;
}

exprt synth_solvert::get_expression(const e_datat &e_data) const
{
  std::vector<exprt> results;
  results.resize(e_data.instructions.size(), nil_exprt());
  assert(!e_data.instructions.empty());

  for(std::size_t pc=0; pc<e_data.instructions.size(); pc++)
  {
    const auto &instruction=e_data.instructions[pc];
    exprt &result=results[pc];

    // constant?

    if(e_data.parameter_types.empty() ||
       get(instruction.constant_sel).is_true())
    {
      result=get(instruction.constant_val);
    }
    else
    {
      result=nil_exprt();

      for(std::size_t i=0; i<instruction.parameter_sel.size(); i++)
        if(get(instruction.parameter_sel[i]).is_true())
        {
          result=exprt(ID_parameter, e_data.parameter_types[i]);
          result.set(ID_identifier, i);
          break;
        }
    }
    
  }

  status() << from_expr(ns, "", e_data.function_symbol)
           << " := "
           << from_expr(ns, "", results.back())
           << eom;

  return results.back();
}

decision_proceduret::resultt synth_solvert::dec_solve()
{
  return BASEt::dec_solve();
}

