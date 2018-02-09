#include "verify.h"
#include "solver.h"

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

  solvert solver_container(use_smt, logic, ns, get_message_handler());
  auto &solver=solver_container.get();

  decision_proceduret::resultt result;

  verify_encodingt verify_encoding;
  verify_encoding.functions=solution.functions;
  verify_encoding.free_variables=problem.free_variables;

  add_problem(verify_encoding, solver);
  result=solver();

  if(result==decision_proceduret::resultt::D_SATISFIABLE)
    counterexample=
      verify_encoding.get_counterexample(solver);
  else
    counterexample.clear();

  return result;
}

void verifyt::add_problem(
  verify_encodingt &verify_encoding,
  decision_proceduret &solver)
{
  for(const auto &e : problem.side_conditions)
  {
    const exprt encoded=verify_encoding(e);
    debug() << "sc: " << from_expr(ns, "", encoded) << eom;
    solver.set_to_true(encoded);
  }

  const exprt encoded=verify_encoding(conjunction(problem.constraints));
  debug() << "co: !(" << from_expr(ns, "", encoded) << ')' << eom;
  solver.set_to_false(encoded);
}

