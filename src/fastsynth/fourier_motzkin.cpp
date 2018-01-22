#include "fourier_motzkin.h"

#include <langapi/language_util.h>

literalt fourier_motzkint::convert_rest(const exprt &expr)
{
  // record
  literalt l=prop.new_variable();
  constraints.push_back(constraintt(l, expr));
  return l;
}

void fourier_motzkint::assignment()
{
  for(const auto &c : constraints)
  {
    tvt value=prop.l_get(c.l);

    debug().width(9);
    debug() << std::left << std::string(value.to_string())+": "
            << from_expr(ns, "", c.expr) << eom;
  }
}

decision_proceduret::resultt fourier_motzkint::dec_solve()
{
  while(true)
  {
    propt::resultt result=prop.prop_solve();

    switch(result)
    {
    case propt::resultt::P_SATISFIABLE:
      assignment();
      return resultt::D_SATISFIABLE;

    case propt::resultt::P_UNSATISFIABLE:
      return resultt::D_UNSATISFIABLE;

    default:
      return resultt::D_ERROR;
    }
  }
}

