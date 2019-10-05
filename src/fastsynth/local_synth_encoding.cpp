#include <fastsynth/local_synth_encoding.h>

#include <util/expr_initializer.h>
#include <util/prefix.h>
#include <util/suffix.h>

#include <algorithm>
#include <iterator>

local_synth_encodingt::local_synth_encodingt(
  const namespacet &ns,
  const solutiont &solution_template,
  const synth_encodingt::constraintst &extra_constraints)
  : ns(ns),
    solution_template(solution_template),
    extra_constraints(extra_constraints)
{
}

symbol_exprt
cval(const irep_idt &identifier, const size_t index, const typet &word_type)
{
  const irep_idt const_val_id(
    id2string(identifier) + '_' + std::to_string(index) + "_cval");
  return symbol_exprt(const_val_id, word_type);
}

namespace
{
/// Replaces constants in a template solution.
class replace_constst : public expr_visitort
{
  /// Identifier of the synthesised function.
  const std::string &identifier;

  /// \see synth_encodingt::e_datat::word_type
  const typet &word_type;

public:
  /// Number of the next constant. Constants are numbered in visitation order.
  size_t constant_index;

  /// Creates a new visitor to replace constants.
  /// \param identifier \see replace_constantst::identifier
  /// \param word_type \see replace_constantst::word_type
  replace_constst(const irep_idt &identifier, const typet &word_type)
    : identifier(id2string(identifier)),
      word_type(word_type),
      constant_index(0u)
  {
  }

  /// \see expr_visitort::operator()(exprt &)
  void operator()(exprt &expr) override
  {
    if(ID_constant == expr.id() && expr.type() == word_type)
      expr = cval(identifier, constant_index++, word_type);
  }
};

/// Replaces parameters in a template solution.
class replace_paramst : public expr_visitort
{
  /// Used to map parameter symbols to their actual arguments.
  const std::map<symbol_exprt, exprt> &actual_params;

public:
  /// Creates a new visitor to replace parameters.
  /// \param actual_params \see replace_constantst::actual_params
  explicit replace_paramst(const std::map<symbol_exprt, exprt> &actual_params)
    : actual_params(actual_params)
  {
  }

  /// \see expr_visitort::operator()(exprt &)
  void operator()(exprt &expr) override
  {
    symbol_exprt *const symbol_expr = expr_try_dynamic_cast<symbol_exprt>(expr);
    if(!symbol_expr)
      return;
    const auto actual_param(actual_params.find(*symbol_expr));
    if(end(actual_params) != actual_param)
      expr = actual_param->second;
  }
};
} // namespace

/// Prefix for synthesis function parameter names.
#define PARAM_PREFIX "synth::parameter"

exprt local_synth_encodingt::operator()(const exprt &expr)
{
  // Add extra constraints first, only once.
  const bool add_extra_constraints = constraints.empty();
  if(add_extra_constraints)
    copy(
      begin(extra_constraints),
      end(extra_constraints),
      back_inserter(synth_encodingt::constraints));

  const function_application_exprt *const func =
    expr_try_dynamic_cast<function_application_exprt>(expr);
  if(func)
  {
    e_datat e_data;
    e_data.return_type = func->type();
    for(const exprt &op : func->arguments())
      e_data.parameter_types.push_back(op.type());
    word_type = e_data.compute_word_type();

    size_t param_index = 0u;
    std::map<symbol_exprt, exprt> actual_params;
    for(const exprt &op : func->arguments())
    {
      const irep_idt name(PARAM_PREFIX + std::to_string(param_index++));
      const symbol_exprt placeholder(name, word_type);
      actual_params.emplace(placeholder, (*this)(op));
    }

    DATA_INVARIANT(func->function().id()==ID_symbol,
      "function must be symbol");
    const irep_idt &identifier = to_symbol_expr(func->function()).get_identifier();
    const std::map<symbol_exprt, exprt>::const_iterator it = find_if(
      begin(solution_template.functions),
      end(solution_template.functions),
      [&identifier](const std::pair<symbol_exprt, exprt> &entry) {
        return identifier == entry.first.get_identifier();
      });
    CHECK_RETURN(end(solution_template.functions) != it);
    exprt result(it->second);
    replace_constst replace_consts(identifier, word_type);
    result.visit(replace_consts);
    replace_paramst replace_params(actual_params);
    result.visit(replace_params);

    // Restrict constant to any of the literals.
    if(add_extra_constraints && !literals.empty())
    {
      for(auto it(begin(literals)); it != end(literals);)
        if(word_type != it->type())
          it = literals.erase(it);
        else
          ++it;

      exprt::operandst options;
      const size_t num_consts = replace_consts.constant_index;
      for(size_t const_index = 0; const_index < num_consts; ++const_index)
      {
        const symbol_exprt c(cval(identifier, const_index, word_type));
        const std::set<constant_exprt>::const_iterator first(begin(literals));
        for(size_t lit_index = 0; lit_index < literals.size(); ++lit_index)
        {
          equal_exprt option(c, *next(first, lit_index));
          options.emplace_back(std::move(option));
        }
      }
      constraints.emplace_back(disjunction(options));
    }
    return result;
  }
  return synth_encodingt::operator()(expr);
}

namespace
{
/// Replaces constant placeholders with values from decision procedure.
class get_constant_assignmentt : public expr_visitort
{
  /// Namespace to create zero expressions if applicable.
  const namespacet &ns;

  /// Decision procedure holding the constant values.
  const decision_proceduret &solver;

  /// \see synth_encodingt::e_datat::word_type
  const typet &word_type;

  /// Number of the next constant. Constants are numbered in visitation order.
  size_t constant_index;

public:
  /// Identifier of the synthesised function.
  std::string identifier;

  /// Creates replacement visitor for constants by their actual value.
  /// \param ns \see get_constant_assignmentt::ns
  /// \param solver \see get_constant_assignmentt::solver
  /// \param word_type \see get_constant_assignmentt::word_type
  get_constant_assignmentt(
    const namespacet &ns,
    const decision_proceduret &solver,
    const typet &word_type)
    : ns(ns), solver(solver), word_type(word_type), constant_index(0u)
  {
  }

  /// \see expr_visitort::operator()(exprt &)
  virtual void operator()(exprt &expr)
  {
    if(ID_constant != expr.id() || expr.type() != word_type)
      return;

    const symbol_exprt value(cval(identifier, constant_index++, word_type));
    const exprt solver_value(solver.get(value));
    if(solver_value.is_nil())
      expr = *zero_initializer(word_type, expr.source_location(), ns);
    else
      expr = solver.get(value);
  }
};
} // namespace

solutiont
local_synth_encodingt::get_solution(const decision_proceduret &solver) const
{
  solutiont result(solution_template);

  for(std::pair<const symbol_exprt, exprt> &function : result.functions)
  {
    const irep_idt &identifier = function.first.get_identifier();
    get_constant_assignmentt get_constant_assignment(ns, solver, word_type);
    get_constant_assignment.identifier = id2string(identifier);
    function.second.visit(get_constant_assignment);
  }

  return result;
}
