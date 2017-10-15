#include "verify_solver.h"

#include <util/arith_tools.h>

bvt verify_solvert::convert_bitvector(const exprt &expr)
{
  if(expr.id()==ID_function_application)
  {
    const auto &e=to_function_application_expr(expr);
    auto e_it=expressions.find(e);
    
    exprt result=e_it==expressions.end()?
      from_integer(0, e.type()):e_it->second;

    return BASEt::convert_bitvector(result);
  }
  else
    return BASEt::convert_bitvector(expr);
}

verify_solvert::argumentst verify_solvert::get_arguments(
  const function_application_exprt &e) const
{
  argumentst result;
  result.resize(e.operands().size(), nil_exprt());

  //for(const auto &p : 
  
  return result;
}

decision_proceduret::resultt verify_solvert::dec_solve()
{
  return BASEt::dec_solve();
}

