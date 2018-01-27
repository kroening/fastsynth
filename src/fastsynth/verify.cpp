#include "verify.h"

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include <langapi/language_util.h>

void verifyt::output(
  const solutiont::functionst &functions,
  std::ostream &out)
{
  for(const auto &f : functions)
  {
    out << f.first.get_identifier()
        << " -> "
        << from_expr(ns, "", f.second)
        << '\n';
  }
}

decision_proceduret::resultt verifyt::operator()(
  solutiont &solution)
{
  output(solution.functions, debug());
  debug() << eom;

  satcheckt verify_satcheck;
  verify_satcheck.set_message_handler(get_message_handler());

  bv_pointerst verify_solver(ns, verify_satcheck);
  verify_solver.set_message_handler(get_message_handler());

  verify_encodingt verify_encoding;
  verify_encoding.functions=solution.functions;
  verify_encoding.free_variables=problem.free_variables;

  add_problem(verify_encoding, verify_solver);

  auto result=verify_solver();

  if(result==decision_proceduret::resultt::D_SATISFIABLE)
    counterexample=
      verify_encoding.get_counterexample(verify_solver);
  else
    counterexample.clear();

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

