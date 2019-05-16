#include "fm_verify.h"

#include "fourier_motzkin.h"

#include "solver.h"

#include <solvers/sat/satcheck.h>

#include <langapi/language_util.h>

#include <util/replace_symbol.h>
#include <util/simplify_expr.h>

void get_symbols(const exprt &src, std::set<symbol_exprt> &dest)
{
  if(src.id()==ID_symbol)
    dest.insert(to_symbol_expr(src));
  else
    for(const auto &op : src.operands())
      get_symbols(op, dest);
}

std::set<symbol_exprt> get_symbols(const exprt &src)
{
  std::set<symbol_exprt> result;
  get_symbols(src, result);
  return result;
}

decision_proceduret::resultt fm_verifyt::operator()(solutiont &solution)
{
  solvert solver_container(use_smt, logic, ns, get_message_handler());
  auto &solver=solver_container.get();

  verify_encodingt verify_encoding;
  verify_encoding.functions=solution.functions;
  verify_encoding.free_variables=problem.free_variables;

  add_problem(verify_encoding, solver);

  auto result=solver();

  if(result==decision_proceduret::resultt::D_SATISFIABLE)
  {
    counterexample=
      verify_encoding.get_counterexample(solver);

    #if 0
    for(const auto &it : counterexample.assignment)
    {
      status() << "COUNTEREXAMPLE: "
               << from_expr(ns, "", it.first)
               << " |-> "
               << from_expr(ns, "", it.second) << eom;
    }
    #endif

    // we might be able to generalize
    for(auto &f_it : solution.s_functions)
      f_it.second=simplify_expr(f_it.second, ns);

    satcheck_no_simplifiert fm_satcheck(get_message_handler());
    fourier_motzkint fm_solver(ns, fm_satcheck, get_message_handler());
    fm_solver.existential_variables=problem.free_variables;

    verify_encodingt fm_encoding;
    fm_encoding.functions=solution.s_functions;
    fm_encoding.free_variables=problem.free_variables;

    add_problem(fm_encoding, fm_solver);

    fm_solver();

    exprt r=fm_solver.get_result();
    status() << "FM RESULT: " << from_expr(ns, "", r) << eom;
    
    // solve this a bit further
    solvert r_solver_container(use_smt, logic, ns, get_message_handler());
    auto &r_solver=r_solver_container.get();
    r_solver.set_to_false(r);

    if(r_solver()==decision_proceduret::resultt::D_UNSATISFIABLE)
      return decision_proceduret::resultt::D_SATISFIABLE; // nope, give up

    // build new solution, try again
    std::set<symbol_exprt> symbols=get_symbols(r);

    replace_symbolt replace_symbol;

    for(const auto &s : symbols)
      replace_symbol.insert(s, r_solver.get(s));

    auto new_solution=solution.functions;

    for(const auto &f_it : solution.s_functions)
    {
      exprt tmp=f_it.second;
      replace_symbol(tmp);
      tmp=simplify_expr(tmp, ns);
      new_solution[f_it.first]=tmp;
    }

    solvert solver2_container(use_smt, logic, ns, get_message_handler());
    auto &solver2=solver2_container.get();

    verify_encodingt verify_encoding2;
    verify_encoding2.functions=new_solution;
    verify_encoding2.free_variables=problem.free_variables;

    add_problem(verify_encoding2, solver2);

    auto result=solver2();

    if(result==decision_proceduret::resultt::D_UNSATISFIABLE)
    {
      status() << "FM found solution!" << eom;
      solution.functions=new_solution;
    }

    return result;
  }
  else
  {
    counterexample.clear();
    return result;
  }
}
