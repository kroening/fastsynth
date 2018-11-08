#include "verify.h"
#include "solver.h"

#include <langapi/language_util.h>

void verifyt::output(
  const solutiont::functionst &functions,
  std::ostream &out)
{
  bool first = true;
  for(const auto &f : functions)
  {
    if(first)
      first = false;
    else
      out << '\n';

    out << f.first.get_identifier()
        << " -> "
        << from_expr(ns, "", f.second);
  }
}

decision_proceduret::resultt verifyt::operator()(
  const solutiont &solution)
{
  status() << green;
  output(solution.functions, status());
  status() << reset << eom;

  // check that the parameters in the given solution
  // are consistent with the function signature
  verify_encodingt::check_function_bodies(solution.functions);

  solvert solver_container(use_smt, logic, ns, get_message_handler());
  auto &solver=solver_container.get();

  decision_proceduret::resultt result;

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
  verify_encoding_baset &verify_encoding,
  decision_proceduret &solver)
{
  verify_encoding.clear();

  for(const auto &e : problem.side_conditions)
  {
    const exprt encoded=verify_encoding(e);
    debug() << "sc: " << from_expr(ns, "", encoded) << eom;
    solver.set_to_true(encoded);
  }

  const exprt encoded=verify_encoding(conjunction(problem.constraints));
  debug() << "co: !(" << from_expr(ns, "", encoded) << ')' << eom;
  solver.set_to_false(encoded);

  for(const auto &c : verify_encoding.constraints)
  {
    solver.set_to_true(c);
    debug() << "ec: " << from_expr(ns, "", c) << eom;
  }
}

