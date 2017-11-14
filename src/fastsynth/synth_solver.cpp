#include "synth_solver.h"

#include <langapi/language_util.h>

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

