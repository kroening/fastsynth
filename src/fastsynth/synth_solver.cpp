#include "synth_solver.h"

#include <langapi/language_util.h>

bvt synth_solvert::convert_bitvector(const exprt &expr)
{
  if(expr.id()==ID_function_application)
  {
    const auto &e=to_function_application_expr(expr);
    const irep_idt identifier=
      e.function().get_identifier();
    
    e_datat &e_data=e_data_map[e];

    unsigned pc=0;
    
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

  for(unsigned pc=0; pc<e_data.instructions.size(); pc++)
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

