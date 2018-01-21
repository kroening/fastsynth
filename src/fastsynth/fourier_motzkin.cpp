#include "fourier_motzkin.h"

literalt fourier_motzkint::convert_rest(const exprt &expr)
{
  // record
  literalt l=prop.new_variable();
  constraints.push_back(constraintt(l, expr));
  return l;
}

decision_proceduret::resultt fourier_motzkint::dec_solve()
{
  while(true)
  {
    propt::resultt result=prop.prop_solve();

    switch(result)
    {
    case propt::resultt::P_SATISFIABLE:
      return resultt::D_SATISFIABLE;

    case propt::resultt::P_UNSATISFIABLE:
      return resultt::D_UNSATISFIABLE;

    default:
      return resultt::D_ERROR;
    }
  }
}

