/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <fastsynth/symex_problem_factory.h>
#include <fastsynth/cegis_types.h>

#include <goto-programs/abstract_goto_model.h>

#include <goto-symex/goto_symex.h>
#include <goto-symex/ssa_step.h>
#include <goto-symex/symex_target_equation.h>

#include <analyses/guard.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/prop/prop_conv.h>
#include <solvers/sat/satcheck.h>

#include <util/expr_iterator.h>
#include <util/simplify_expr.h>

/// Symbolically executes the synthesis specification.
/// \param new_symbol_table Output symbol table for symexed symbols.
/// \param equation Output decision procedure formula.
/// \param options Symbolic execution options.
/// \param model GOTO model to symex.
static void symex(
  message_handlert &msg,
  symbol_tablet &new_symbol_table,
  symex_target_equationt &equation,
  const optionst &options,
  abstract_goto_modelt &model)
{
  const symbol_tablet &symbol_table = model.get_symbol_table();
  path_lifot path_storage;
  guard_managert guard_manager;
  goto_symext goto_symex(
    msg, symbol_table, equation, options, path_storage, guard_manager);

  auto get_goto_function = [&model](const irep_idt &id) ->
    const goto_functionst::goto_functiont &
    {
      return model.get_goto_function(id);
    };

  goto_symex.symex_from_entry_point_of(get_goto_function, new_symbol_table);
}

/// Indicates whether the given step is part of the CEGIS constraint.
/// \param step Step to inspect.
/// \return <code>true</code> if the given step is an assumption or assertion,
///   <code>false</code> otherwise.
static bool is_assert_or_assume(const SSA_stept &step)
{
  return step.is_assert() || step.is_assume();
}

/// Indicates whether the given step is a CEGIS side condition.
/// \param step Step to inspect.
/// \return <code>true</code> if the given step is not part of the CEGIS
///   constraint, <code>false</code> otherwise.
static bool is_side_condition(const SSA_stept &step)
{
  return !is_assert_or_assume(step);
}

namespace
{
/// Filters steps in a symex_target_equationt::SSA_stepst container when
/// processed by symex_target_equationt::convert(prop_convt &).
class step_filtert
{
  /// Steps container to filter.
  symex_target_equationt::SSA_stepst &steps;

  /// Previously disabled steps.
  std::vector<SSA_stept *> disabled;

  /// Previously disabled assertions.
  std::vector<SSA_stept *> disabled_assertions;

  /// Remove a previously applied filter.
  void undo_previous_ignore()
  {
    for(SSA_stept *step : disabled)
      step->ignore = false;
    disabled.clear();

    for(SSA_stept *step : disabled_assertions)
      step->type = goto_trace_stept::typet::ASSERT;
    disabled_assertions.clear();
  }

public:
  /// Filters the given steps.
  /// \param steps \see step_filtert::steps
  explicit step_filtert(symex_target_equationt::SSA_stepst &steps)
    : steps(steps)
  {
  }

  /// Disables all steps which match the given filter predicate.
  /// \param pred Predicate using which to filter.
  void ignore(bool (*const pred)(const SSA_stept &))
  {
    undo_previous_ignore();

    for(SSA_stept &step : steps)
      if(pred(step))
      {
        step.ignore = true;
        disabled.push_back(&step);
        if(step.is_assert())
        {
          step.type = goto_trace_stept::typet::ASSUME;
          disabled_assertions.push_back(&step);
        }
      }
  }
};

/// Hash code wrapper for literalt.
class literal_hasht
{
public:
  /// \see literalt::l
  /// \param l Literal for which to generate a hash code.
  /// \return <code>l.get()</code>
  size_t operator()(const literalt &l) const
  {
    return static_cast<size_t>(l.get());
  }
};

/// Replace guard and assumption literals by their actual constraints in CEGIS
/// constraint components.
class replace_literalst : public expr_visitort
{
  /// Previously converted expressions and their associated literals.
  const std::unordered_map<literalt, exprt, literal_hasht> &expressions;

public:
  /// Replaces the provided literals when visited.
  /// \param expressions \see replace_literalst::expressions
  replace_literalst(
    const std::unordered_map<literalt, exprt, literal_hasht> &expressions)
    : expressions(expressions)
  {
  }

  /// \see expr_visitort::operator()(exprt &)
  void operator()(exprt &expr) override
  {
    if(ID_literal == expr.id())
      expr = expressions.at(to_literal_expr(expr).get_literal());
  }
};

/// Converts SSA instructions relevant to the CEGIS constraint portion into
/// CEGIS problemt components.
class constraints_convt : public bv_pointerst
{
  /// Dummy propt for problem conversion. Generated SAT constraint is ignored.
  satcheckt prop;

  /// Problem into which to insert generated constraints.
  problemt &problem;

  /// Indicates whether the single assertion or the general purpose constraint
  /// generation strategy in
  /// symex_target_equationt::convert_assertions(prop_conv &) is used.
  const bool is_single_assertion;

  /// Tracking assumptions for the single assertion in single assertion mode.
  exprt::operandst assumptions;

  /// Tracking previously translated expressions and their literals in general
  /// multi-assertion mode.
  std::unordered_map<literalt, exprt, literal_hasht> expressions;

public:
  /// Inserts generated constraints into the given problem.
  /// \param problem \see constraints_convt::problem
  /// \param ns Namespace to forward to nested prop_convt instances.
  /// \param is_single_assertion \see constraints_convt::is_single_assertion
  constraints_convt(
    problemt &problem,
    const namespacet &ns,
    const bool is_single_assertion,
    message_handlert &_message_handler)
    : bv_pointerst(ns, prop, _message_handler),
      prop(_message_handler),
      problem(problem),
      is_single_assertion(is_single_assertion)
  {
  }

  /// \see decision_proceduret::set_to(const exprt &, bool)
  void set_to(const exprt &expr, const bool value) override
  {
    if(is_single_assertion)
    {
      if(value)
        assumptions.push_back(expr);
      else
        problem.constraints.push_back(
          assumptions.empty() ? expr
                              : implies_exprt(conjunction(assumptions), expr));
    }
    else
    {
      PRECONDITION(value);
      PRECONDITION(ID_or == expr.id());
      exprt::operandst constraints(expr.operands());
      replace_literalst replace_literals(expressions);
      for(exprt &constraint : constraints)
      {
        constraint = to_not_expr(constraint).op();
        constraint.visit(replace_literals);
      }

      copy(
        begin(constraints),
        end(constraints),
        back_inserter(problem.constraints));
    }
  }

  /// \see prop_convt::convert(const exprt &)
  literalt convert(const exprt &expr) override
  {
    const literalt literal(bv_pointerst::convert(expr));
    if(!is_single_assertion)
      expressions.emplace(literal, expr);

    return literal;
  }
};

/// Converts SSA instructions relevant to the CEGIS side conditions portion into
/// CEGIS problemt components.
class side_conditions_convt : public bv_pointerst
{
  /// Dummy propt for problem conversion. Generated SAT constraint is ignored.
  satcheckt prop;

  /// Problem into which to insert generated constraints.
  problemt &problem;

public:
  /// Inserts generated conditions into the given problem.
  /// \param problem \see side_conditions_convt::problem
  /// \param ns Namespace to forward to nested prop_convt instances.
  explicit side_conditions_convt(
    problemt &problem,
    const namespacet &ns,
    message_handlert &_message_handler)
    : bv_pointerst(ns, prop, _message_handler),
      prop(_message_handler),
      problem(problem)
  {
  }

  /// \see decision_proceduret::set_to(const exprt &, bool)
  void set_to(const exprt &expr, const bool value) override
  {
    const exprt &sc = value ? expr : simplify_expr(not_exprt(expr), ns);
    problem.side_conditions.push_back(sc);
  }
};
}

/// Retrieves all free variables in the given expression.
/// \param free_variables Container with all free variables to extend.
/// \param expr Expression in which to search for free variables.
static void
get_free_variables(std::set<exprt> &free_variables, const exprt &expr)
{
  copy_if(
    expr.unique_depth_cbegin(),
    expr.unique_depth_cend(),
    inserter(free_variables, end(free_variables)),
    [](const exprt &expr) { return ID_nondet_symbol == expr.id(); });
}

problemt to_problem(
  message_handlert &msg,
  const optionst &options,
  abstract_goto_modelt &model)
{
  symbol_tablet new_sym_tab;
  symex_target_equationt equation(msg);
  symex(msg, new_sym_tab, equation, options, model);

  const namespacet ns(model.get_symbol_table());
  problemt result;
  step_filtert step_filter(equation.SSA_steps);
  step_filter.ignore(is_assert_or_assume);
  side_conditions_convt side_conditions_conv(result, ns, msg);
  equation.convert(side_conditions_conv);

  step_filter.ignore(is_side_condition);
  const bool is_single_assertion = equation.count_assertions() == 1u;
  constraints_convt constraints_conv(result, ns, is_single_assertion, msg);
  equation.convert(constraints_conv);

  for(const exprt &c : result.constraints)
    get_free_variables(result.free_variables, c);

  for(const exprt &c : result.side_conditions)
    get_free_variables(result.free_variables, c);

  return result;
}
