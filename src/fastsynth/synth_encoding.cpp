#include "synth_encoding.h"

exprt e_datat::instructiont::result(
  const std::vector<exprt> &arguments)
{
  exprt result_expr=constant_val; // last resort

  assert(arguments.size()==parameter_sel.size());

  for(std::size_t i=0; i<parameter_sel.size(); i++)
  {
    exprt selector=parameter_sel[i];
    result_expr=if_exprt(selector, arguments[i], result_expr);
  }

  return result_expr;
}

void e_datat::setup(
  const function_application_exprt &e)
{
  if(setup_done) return;
  setup_done=true;

  function_symbol=e.function();
  const irep_idt &identifier=function_symbol.get_identifier();

  const auto &arguments=e.arguments();
  parameter_types.resize(arguments.size());
  for(std::size_t i=0; i<parameter_types.size(); i++)
    parameter_types[i]=arguments[i].type();

  instructions.reserve(1);

  for(std::size_t pc=0; pc<1; pc++)
  {
    instructions.push_back(instructiont(pc));
    auto &instruction=instructions[pc];

    // constant
    irep_idt const_val_id=id2string(identifier)+"_"+std::to_string(pc)+"_cval";
    instruction.constant_val=symbol_exprt(const_val_id, e.type());

    // one of the arguments
    instruction.parameter_sel.resize(arguments.size());

    for(std::size_t i=0; i<arguments.size(); i++)
    {
      irep_idt param_sel_id=id2string(identifier)+"_"+
               std::to_string(pc)+"_p"+std::to_string(i)+"sel";
      instruction.parameter_sel[i]=symbol_exprt(param_sel_id, bool_typet());
    }
  }
}

exprt e_datat::result(
  const std::vector<exprt> &arguments)
{
  std::vector<exprt> results;
  results.resize(instructions.size());

  for(std::size_t pc=0; pc<instructions.size(); pc++)
    results[pc]=instructions[pc].result(arguments);

  assert(!results.empty());

  return results.back();
}

exprt e_datat::get_expression(
  const decision_proceduret &solver) const
{
  assert(!instructions.empty());

  std::vector<exprt> results;
  results.resize(instructions.size(), nil_exprt());

  for(std::size_t pc=0; pc<instructions.size(); pc++)
  {
    const auto &instruction=instructions[pc];
    exprt &result=results[pc];

    // a parameter?

    result=nil_exprt();

    for(std::size_t i=0; i<instruction.parameter_sel.size(); i++)
      if(solver.get(instruction.parameter_sel[i]).is_true())
      {
        result=exprt(ID_parameter, parameter_types[i]);
        result.set(ID_identifier, i);
        break;
      }

    if(result.is_nil())
    {
      // constant, this is the last resort
      result=solver.get(instruction.constant_val);
    }
  }

  return results.back();
}

exprt synth_encodingt::operator()(const exprt &expr)
{
  if(expr.id()==ID_function_application)
  {
    auto tmp=to_function_application_expr(expr);

    // apply recursively to arguments
    for(auto &op : tmp.arguments())
      op=(*this)(op);

    e_datat &e_data=e_data_map[tmp.function()];
    exprt final_result=e_data(tmp);

    return final_result;
  }
  else if(expr.id()==ID_symbol)
  {
    // add the suffix
    symbol_exprt tmp=to_symbol_expr(expr);
    tmp.set_identifier(id2string(tmp.get_identifier())+suffix);
    return tmp;
  }
  else
  {
    exprt tmp=expr;

    for(auto &op : tmp.operands())
      op=(*this)(op); // recursive call

    return tmp;
  }
}

exprt synth_encodingt::get_expression(
  const symbol_exprt &function_symbol,
  const decision_proceduret &solver) const
{
  const auto it=e_data_map.find(function_symbol);
  if(it==e_data_map.end()) return nil_exprt();
  return it->second.get_expression(solver);
}

std::map<symbol_exprt, exprt> synth_encodingt::get_expressions(
  const decision_proceduret &solver) const
{
  std::map<symbol_exprt, exprt> result;

  for(const auto &it : e_data_map)
  {
    result[it.first]=it.second.get_expression(solver);
  }

  return result;
}

