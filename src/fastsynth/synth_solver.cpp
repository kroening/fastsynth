#include "synth_solver.h"

#include <langapi/language_util.h>

exprt synth_solvert::e_datat::instructiont::result_constraint(
  const irep_idt &identifier)
{
  std::size_t sel_count=0;

  for(auto &o : options)
  {
    irep_idt sel_id=id2string(identifier)+"_s"+
      std::to_string(pc)+"_"+std::to_string(sel_count);
    o.sel=symbol_exprt(sel_id, bool_typet());
  }

  // make the last one 'true'
  if(!options.empty())
    options.back().sel=true_exprt();

  exprt result_expr=nil_exprt();
  exprt selector=nil_exprt();

  for(const auto &o : options)
  {
    if(result_expr.is_nil())
      result_expr=o.expr;
    else
      result_expr=if_exprt(selector, result_expr, o.expr);

    selector=o.sel;
    sel_count++;
  }

  result_symbol=symbol_exprt(
    id2string(identifier)+"_r"+std::to_string(pc),
    result_expr.type());

  return equal_exprt(result_symbol, result_expr);
}

bvt synth_solvert::convert_bitvector(const exprt &expr)
{
  if(expr.id()==ID_function_application)
  {
    const auto &e=to_function_application_expr(expr);
    const irep_idt identifier=
      e.function().get_identifier();

    e_datat &e_data=e_data_map[e];

    std::size_t pc=0;
    
    e_data.instructions.push_back(e_datat::instructiont(pc));
    auto &instruction=e_data.instructions.back();
    
    irep_idt const_id=id2string(identifier)+"_c"+std::to_string(pc);
    symbol_exprt constant_value(const_id, expr.type());
    instruction.add_option(constant_value);

    const auto &arguments=e.arguments();

    for(const auto &arg : arguments)
      if(arg.type()==e.type())
        instruction.add_option(arg);
      else
        instruction.add_option(typecast_exprt(arg, e.type()));

    exprt constraint=instruction.result_constraint(identifier);
    set_to_true(constraint);

    status() << "Constraint: " << from_expr(ns, "", constraint) << eom;

    assert(!e_data.instructions.empty());

    symbol_exprt final_result=
      e_data.instructions.back().result_symbol;
    
    return BASEt::convert_bitvector(final_result);
  }
  else
    return BASEt::convert_bitvector(expr);
}

std::map<function_application_exprt, exprt> synth_solvert::get_expressions() const
{
  std::map<function_application_exprt, exprt> result;

  for(const auto &e : e_data_map)
    result[e.first]=
      get_expression(e.first, e.second);

  return result;
}

exprt synth_solvert::get_expression(
  const function_application_exprt &e,
  const e_datat &e_data) const
{
  std::vector<exprt> results;
  results.resize(e_data.instructions.size(), nil_exprt());
  assert(!e_data.instructions.empty());

  for(std::size_t pc=0; pc<e_data.instructions.size(); pc++)
  {
    const auto &instruction=e_data.instructions[pc];
    exprt &result=results[pc];

    for(const auto &o : instruction.options)
    {
      exprt sel_value=get(o.sel);
      if(sel_value.is_true())
      {
        result=get(o.expr);
        break;
      }
    }
    
    status() << from_expr(ns, "", instruction.result_symbol)
             << " := "
             << from_expr(ns, "", result)
             << eom;
  }

  return results.back();
}

decision_proceduret::resultt synth_solvert::dec_solve()
{
  return BASEt::dec_solve();
}

