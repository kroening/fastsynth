#include <fastsynth/local_synth_encoding.h>

#include <util/prefix.h>
#include <util/suffix.h>

local_synth_encodingt::local_synth_encodingt(
  const std::map<symbol_exprt, exprt> &solution_template,
  const synth_encodingt::constraintst &constraints)
  : solution_template(solution_template), constraints(constraints)
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
/// Replaces parameters and constants in a template solution.
class replace_params_and_constst : public expr_visitort
{
  /// Used to map parameter symbols to their actual arguments.
  const std::map<symbol_exprt, exprt> actual_params;

  /// Identifier of the synthesised function.
  const std::string &identifier;

  /// \see synth_encodingt::e_datat::word_type
  const typet &word_type;

  /// Number of the next constant. Constants are numbered in visitation order.
  size_t constant_index;
public:
  /// Creates a new visitor to replace constants and parameters.
  /// \param actual_params
  ///   \see replace_constantst::actual_params
  /// \param identifier \see replace_constantst::identifier
  /// \param word_type \see replace_constantst::word_type
  replace_params_and_constst(
    const std::map<symbol_exprt, exprt> &actual_params,
    const irep_idt &identifier,
    const typet &word_type)
    : actual_params(actual_params),
      identifier(id2string(identifier)),
      word_type(word_type),
      constant_index(0u)
  {
  }

  /// \see expr_visitort::operator()(exprt &)
  virtual void operator()(exprt &expr)
  {
    if(ID_constant == expr.id())
    {
      expr = cval(identifier, constant_index++, word_type);
      return;
    }

    symbol_exprt *const symbol_expr = expr_try_dynamic_cast<symbol_exprt>(expr);
    if(!symbol_expr)
      return;
    const auto actual_param(actual_params.find(*symbol_expr));
    if(end(actual_params) == actual_param)
      return;
    expr = actual_param->second;
  }
};
}

/// Prefix for synthesis function parameter names.
#define PARAM_PREFIX "synth::parameter"

exprt local_synth_encodingt::operator()(const exprt &expr)
{
  // Add extra constraints first, only once.
  if(synth_encodingt::constraints.empty())
    copy(
      begin(constraints),
      end(constraints),
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

    const irep_idt &identifier=func->function().get_identifier();
    const std::map<symbol_exprt, exprt>::const_iterator it(
      solution_template.find(symbol_exprt(identifier, code_typet())));
    CHECK_RETURN(end(solution_template) != it);
    exprt result(it->second);
    replace_params_and_constst replace(actual_params, identifier, word_type);
    result.visit(replace);
    return result;
  }
  return synth_encodingt::operator()(expr);
}

namespace
{
/// Replaces constant placeholders with values from decision procedure.
class get_constant_assignmentt : public expr_visitort
{
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
  /// \param solver \see get_constant_assignmentt::solver
  /// \param word_type \see get_constant_assignmentt::word_type
  get_constant_assignmentt(
    const decision_proceduret &solver,
    const typet &word_type)
    : solver(solver), word_type(word_type), constant_index(0u)
  {
  }

  /// \see expr_visitort::operator()(exprt &)
  virtual void operator()(exprt &expr)
  {
    if(ID_constant != expr.id())
      return;

    const symbol_exprt value(cval(identifier, constant_index++, word_type));
    expr = solver.get(value);
  }
};
}

std::map<symbol_exprt, exprt>
local_synth_encodingt::get_expressions(const decision_proceduret &solver) const
{
  std::map<symbol_exprt, exprt> result(solution_template);

  get_constant_assignmentt get_constant_assignment(solver, word_type);
  for(std::pair<const symbol_exprt, exprt> &function : result)
  {
    const irep_idt &identifier = function.first.get_identifier();
    get_constant_assignment.identifier = id2string(identifier);
    function.second.visit(get_constant_assignment);
  }

  return result;
}

synth_encoding_factoryt local_synth_encoding(
  const std::map<symbol_exprt, exprt> &solution,
  const synth_encodingt::constraintst &constraints)
{
  return [&]()
  {
    return std::unique_ptr<synth_encodingt>(
      new local_synth_encodingt(solution, constraints));
  };
}
