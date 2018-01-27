#include "verify.h"

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include <langapi/language_util.h>

void output_expressions(
  const std::map<symbol_exprt, exprt> &expressions,
  const namespacet &ns,
  std::ostream &out)
{
  for(const auto &e : expressions)
  {
    out << e.first.get_identifier()
        << " -> "
        << from_expr(ns, "", e.second)
        << '\n';
  }
}

decision_proceduret::resultt verifyt::operator()(
  const std::map<symbol_exprt, exprt> &expressions)
{
  output_expressions(expressions, ns, debug());
  debug() << eom;

  satcheckt verify_satcheck;
  verify_satcheck.set_message_handler(get_message_handler());

  bv_pointerst verify_solver(ns, verify_satcheck);
  verify_solver.set_message_handler(get_message_handler());

  verify_encodingt verify_encoding;
  verify_encoding.expressions=expressions;
  verify_encoding.free_variables=problem.free_variables;

  add_problem(verify_encoding, verify_solver);

  counterexample.clear();

  auto result=verify_solver();

  if(result==decision_proceduret::resultt::D_SATISFIABLE)
    counterexample=
      verify_encoding.get_counterexample(verify_solver);

  return result;
}

void verifyt::add_problem(
  verify_encodingt &verify_encoding,
  prop_convt &prop_conv)
{
  for(const auto &e : problem.side_conditions)
  {
    const exprt encoded=verify_encoding(e);
    debug() << "sc: " << from_expr(ns, "", encoded) << eom;
    prop_conv.set_to_true(encoded);
  }

  const exprt encoded=verify_encoding(conjunction(problem.constraints));
  debug() << "co: !(" << from_expr(ns, "", encoded) << ')' << eom;
  prop_conv.set_to_false(encoded);
}

