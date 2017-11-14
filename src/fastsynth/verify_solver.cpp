#include "verify_solver.h"

#include <util/arith_tools.h>

#include <langapi/language_util.h>

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

std::map<function_application_exprt, exprt::operandst>
  verify_solvert::get_counterexample()
{
  std::map<function_application_exprt, exprt::operandst> result;

  // iterate over arguments, and get their value
  for(const auto &app : applications)
  {
    const auto &arguments=app.arguments();
    exprt::operandst values;
    values.reserve(arguments.size());

    for(const auto &argument : arguments)
    {
      exprt value=get(argument);
      values.push_back(value);
    }

    result[app]=values;

    status() << "CE for " << from_expr(ns, "", app) << ':';
    for(const auto &v : values)
      status() << ' ' << from_expr(ns, "", v);

    status() << eom;
  }

  return result;
}

