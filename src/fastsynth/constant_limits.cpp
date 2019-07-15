#include <fastsynth/constant_limits.h>
#include <fastsynth/cegis.h>
#include <fastsynth/local_synth_encoding.h>

#include <solvers/smt2/smt2_dec.h>

#include <langapi/language_util.h>

#include <util/expr_initializer.h>
#include <util/expr_iterator.h>
#include <util/mathematical_types.h>
#include <util/prefix.h>
#include <util/suffix.h>
#include <util/version.h>

constant_limitst::constant_limitst(
  message_handlert &msg,
  const namespacet &ns,
  const problemt &problem,
  const solutiont &solution_template)
  : messaget(msg),
    ns(ns),
    problem(problem),
    solution_template(solution_template)
{
}

/// Indicates whether a variable is a component describing the synthesised
/// program. This includes constants (`EXPRESSION_*_cval`) and instruction
/// selectors (`EXPRESSION_*_p*sel`), but not temporary expression result
/// variables (`EXPRESSION_*_result_*`).
/// \param name Variable name to test.
/// \return <code>true</code> if the variable describes the synthesised program,
///   <code>false</code> otherwise.
static bool is_program_component(const std::string &name)
{
  if(!has_prefix(name, "EXPRESSION") && !has_prefix(name, "synth_fun::"))
    return false;

  return std::string::npos != name.find("cval") ||
         std::string::npos != name.find("sel");
}

/// Finds variables which are part of the transition relation. These variables
/// are not globally existentially quantified, such as the program component
/// variables like `EXPRESSION_0_p0sel` or `EXPRESSION_0_cval`, because they
/// only need to be consistent with the transition relation in the context of a
/// specific counterexample.
/// \param ops Constraints in which to search for variables.
/// \param free_vars Free variables to be excluded.
/// \return All variables which are part of the transition relation.
static std::set<symbol_exprt>
find_program_vars(const exprt::operandst &ops, const std::set<exprt> &free_vars)
{
  std::set<symbol_exprt> result;
  for(const exprt &op : ops)
  {
    for(auto it = op.unique_depth_cbegin(); it != op.unique_depth_cend(); ++it)
    {
      const symbol_exprt *const sym = expr_try_dynamic_cast<symbol_exprt>(*it);
      if(!sym)
        continue;

      const std::string &id = id2string(sym->get_identifier());
      if(is_program_component(id))
        continue;

      /// Free symbols are not program state variables.
      const std::set<exprt>::const_iterator free_var =
        find_if(begin(free_vars), end(free_vars), [&id](const exprt &expr)
        {
          const symbol_exprt *const free_var =
            expr_try_dynamic_cast<symbol_exprt>(expr);
          if(!free_var)
            return false;

          std::string rhs(id2string(free_var->get_identifier()));
          rhs += "$ce";
          return id == rhs;
        });
      if(end(free_vars) == free_var)
        result.emplace(*sym);
    }
  }
  return result;
}

decision_proceduret::resultt constant_limitst::decide(
  const synth_encodingt::constraintst &additional_constraints)
{
  local_synth_encodingt encoding(ns, solution_template, additional_constraints);
  encoding.suffix = "$ce";
  encoding.constraints.clear();

  exprt::operandst constraints;
  for(const exprt &e : problem.side_conditions)
  {
    const exprt encoded(encoding(e));
    debug() << "sc: " << from_expr(ns, "", encoded) << messaget::eom;
    constraints.emplace_back(encoded);
  }

  for(const exprt &e : problem.constraints)
  {
    const exprt encoded(encoding(e));
    debug() << "co: " << from_expr(ns, "", encoded) << messaget::eom;
    constraints.emplace_back(encoded);
  }

  for(const exprt &c : encoding.constraints)
  {
    constraints.emplace_back(c);
    debug() << "ec: " << from_expr(ns, "", c) << messaget::eom;
  }

  exprt constraint(conjunction(constraints));

  // Existentially quantify non-EXPRESSION_ symbols per counterexample.
  const std::set<symbol_exprt> transition(
    find_program_vars(constraints, problem.free_variables));
  for(const symbol_exprt &user_var : transition)
  {
    const irep_idt &name = user_var.get_identifier();
    exists_exprt quantifier(symbol_exprt(name, user_var.type()), constraint);
    quantifier.type() = constraint.type();
    constraint = quantifier;
  }

  // Universally quantify all counterexample variables.
  for(const exprt &free_var : problem.free_variables)
  {
    const nondet_symbol_exprt *const nondet =
      expr_try_dynamic_cast<nondet_symbol_exprt>(free_var);

    std::string name;
    typet type;
    if(nondet)
    {
      name = "nondet_";
      name += id2string(nondet->get_identifier());
      name += "$ce";
      type = nondet->type();
    }
    else
    {
      const symbol_exprt &var = to_symbol_expr(free_var);
      name = id2string(var.get_identifier());
      name += "$ce";
      type = var.type();
    }

    const symbol_exprt symbol(name, std::move(type));

    forall_exprt quantifier(symbol, constraint);
    quantifier.type() = constraint.type();
    constraint = quantifier;
  }

  std::string notes("Generated by CBMC ");
  notes += CBMC_VERSION;
  smt2_dect prop_conv(ns, "cbmc", notes, "", smt2_dect::solvert::Z3);
  prop_conv.set_message_handler(get_message_handler());
  prop_conv.set_to_true(constraint);

  solutiont::functionst &functions = solution.functions;
  const decision_proceduret::resultt result = prop_conv();
  switch(result)
  {
  case decision_proceduret::resultt::D_UNSATISFIABLE:
    debug() << "SMT unsat, learning new constraints:\n";
    for(const exprt &constraint : additional_constraints)
      debug() << from_expr(ns, "", constraint) << '\n';
    debug() << "for solution:\n";
    output_expressions(solution_template.functions, ns, debug());
    debug() << eom;

    {
      copy(
        begin(additional_constraints),
        end(additional_constraints),
        back_inserter(result_constraints));
    }
    break;
  case decision_proceduret::resultt::D_SATISFIABLE:
    status() << "VERIFICATION SUCCESSFUL\n";
    debug() << "SMT sat, have solution:\n";
    solution = encoding.get_solution(prop_conv);
    for(std::pair<const symbol_exprt, exprt> &expression : functions)
    {
      exprt &value = expression.second;
      if(value.is_nil())
      {
        const typet &expression_type = expression.first.type();
        typet return_type;
        if(ID_code == expression_type.id())
          return_type = to_code_type(expression_type).return_type();
        else
        {
          const mathematical_function_typet &function_type =
            static_cast<const mathematical_function_typet &>(expression_type);
          return_type = function_type.codomain();
        }
        const source_locationt &loc = expression.first.source_location();
        value = *zero_initializer(return_type, loc, ns);
      }
    }
    output_expressions(functions, ns, debug());
    debug() << eom;
    break;
  default:
  case decision_proceduret::resultt::D_ERROR:
    debug() << "SMT error/timeout, learning nothing..." << eom;
    break;
  }

  return result;
}

namespace
{
/// Finds constants in visitation order. This order is important, since it's
/// the order in which the `local_synth_encodingt` labels its constant
/// placeholder variables.
class find_constantst : public const_expr_visitort
{
public:
  /// Constant values in visitation order.
  std::vector<constant_exprt> values;

  /// \see const_expr_visitort::operator()(const exprt &)
  void operator()(const exprt &expr) override
  {
    const constant_exprt *const constant_expr =
      expr_try_dynamic_cast<constant_exprt>(expr);
    if(constant_expr && ID_bool != constant_expr->type().id())
      values.emplace_back(*constant_expr);
  }
};
}

decision_proceduret::resultt constant_limitst::
operator()(const solutiont &candidate)
{
  const solutiont::functionst &functions = candidate.functions;
  debug() << "Testing constants:\n";
  output_expressions(functions, ns, debug());
  debug() << eom;

  find_constantst find_constants;
  for(const std::pair<symbol_exprt, exprt> &expression : functions)
  {
    const irep_idt &name = expression.first.get_identifier();
    expression.second.visit(find_constants);
    for(size_t i = 0u; i < find_constants.values.size(); ++i)
    {
      const constant_exprt &value = find_constants.values.at(i);
      const symbol_exprt constant(cval(name, i, value.type()));

      debug() << "Testing constant:\n";
      debug() << from_expr(ns, name, constant) << '=';
      debug() << from_expr(ns, name, value) << eom;

      const decision_proceduret::resultt below_result(
        decide({binary_predicate_exprt(constant, ID_lt, value)}));
      const decision_proceduret::resultt above_result(
        decide({binary_predicate_exprt(constant, ID_gt, value)}));

      if(
        decision_proceduret::resultt::D_UNSATISFIABLE == below_result &&
        decision_proceduret::resultt::D_UNSATISFIABLE == above_result)
      {
        return decision_proceduret::resultt::D_UNSATISFIABLE;
      }

      if(
        decision_proceduret::resultt::D_SATISFIABLE == below_result ||
        decision_proceduret::resultt::D_SATISFIABLE == above_result)
      {
        return decision_proceduret::resultt::D_SATISFIABLE;
      }
    }
  }

  return decision_proceduret::resultt::D_ERROR;
}
