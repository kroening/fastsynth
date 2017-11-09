#include "verify_solver.h"

#include <util/arith_tools.h>

bvt verify_solvert::convert_bitvector(const exprt &expr)
{
  if(expr.id()==ID_function_application)
  {
    const auto &e=to_function_application_expr(expr);
    applications.insert(e);

    auto e_it=expressions.find(e.function());
    
    exprt result=e_it==expressions.end()?
      from_integer(0, e.type()):e_it->second;

    // need to instantiate parameters with arguments
    exprt instance=instantiate(result, e);

    return BASEt::convert_bitvector(instance);
  }
  else
    return BASEt::convert_bitvector(expr);
}

exprt verify_solvert::instantiate(
  const exprt &expr,
  const function_application_exprt &e)
{
  return expr;
}

decision_proceduret::resultt verify_solvert::dec_solve()
{
  return BASEt::dec_solve();
}

std::map<function_application_exprt, exprt> verify_solvert::get_counterexample()
{
  return {};
}

