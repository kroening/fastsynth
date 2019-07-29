/*******************************************************************\

 Module: Fastsynth Boolean Synth Encoding

 Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

#include "bool_synth_encoding.h"

#include <util/bv_arithmetic.h>
#include <util/config.h>
#include <util/std_types.h>

#include <algorithm>
#include <iostream>
#include <iterator>

/// Used to indicate that the ID is a selector.
#define SELECTOR_FLAG "sel"

/// Separates function name, selector ID and other tags from each other.
#define SELECTOR_SEPARATOR '_'

/// Prefix of a parameter, used in selector names.
#define PARAMETER_PREFIX 'p'

/// Prefix of a unary operation, used in selector names.
#define UNARY_PREFIX 'u'

/// Prefix of a binary operation, used in selector names.
#define BINARY_PREFIX 'b'

/// Prefix of a constant, used in selector names.
#define CONSTANT_TAG "cval"

/// Prefix of a decoded parameter, used when generating solutions.
#define DECODED_PARAMETER_PREFIX "synth::parameter"

/// Prefix of different instances, used in results.
#define INSTANCE_PREFIX "inst"

/// Tag to indicate that the affected ID belongs to a result.
#define RESULT_TAG "result"

/// Names of all supported unary operations.
static const irep_idt unary_ops[] = {
  ID_not,
};

/// Names of all supported binary operations.
static const irep_idt binary_ops[] = {
  ID_or,
  ID_and,
  ID_equal,
  ID_notequal,
};

/// Adds all arguments and constants of this expression to the given
/// instruction.
/// \param [out] instruction: Instruction to add the options to.
/// \param current_program_size: Maximum number of allowed operands for the
///   current iteration.
/// \param function_identifier: Name of the synthesised expression.
/// \param argument_and_literal_count: Sum of the number of arguments and
///   literals.
static void add_arguments_and_constants(
  bool_e_datat::instructiont &instruction,
  const size_t &current_program_size,
  const irep_idt &function_identifier,
  const size_t argument_and_literal_count)
{
  for(std::size_t i = 0; i < argument_and_literal_count; ++i)
  {
    const irep_idt param_sel_id{
      id2string(function_identifier) + SELECTOR_SEPARATOR +
      std::to_string(current_program_size) + SELECTOR_SEPARATOR +
      PARAMETER_PREFIX + std::to_string(i) + SELECTOR_FLAG};
    bool_e_datat::instructiont::optiont &option =
      instruction.add_option(param_sel_id);
    option.kind = bool_e_datat::instructiont::optiont::PARAMETER;
    option.parameter_number = i;
  }
}

/// Adds all unary options supported by this module to the given instruction.
/// \param [out] instruction: Instruction to add the options to.
/// \param current_program_size: Maximum number of allowed operands for the
///   current iteration.
/// \param function_identifier: Name of the synthesised expression.
static void add_unary_options(
  bool_e_datat::instructiont &instruction,
  const size_t &current_program_size,
  const irep_idt &function_identifier)
{
  std::size_t unary_option_index = 0;

  for(const irep_idt operation : unary_ops)
    for(std::size_t operand0 = 0; operand0 < current_program_size; ++operand0)
    {
      const irep_idt sel_id{
        id2string(function_identifier) + SELECTOR_SEPARATOR +
        std::to_string(current_program_size) + SELECTOR_SEPARATOR +
        UNARY_PREFIX + std::to_string(unary_option_index) + SELECTOR_FLAG};

      bool_e_datat::instructiont::optiont &option =
        instruction.add_option(sel_id);
      option.operand0 = operand0;
      option.operation = operation;
      option.kind = bool_e_datat::instructiont::optiont::UNARY;
      unary_option_index++;
    }
}

/// Adds all binary options supported by this module to the given instruction.
/// \param [out] instruction: Instruction to add the options to.
/// \param current_program_size: Maximum number of allowed operands for the
///   current iteration.
/// \param function_identifier: Name of the synthesised expression.
static void add_binary_options(
  bool_e_datat::instructiont &instruction,
  const size_t &current_program_size,
  const irep_idt &function_identifier)
{
  std::size_t binary_option_index = 0;

  for(const irep_idt operation : binary_ops)
    for(std::size_t operand0 = 0; operand0 < current_program_size; ++operand0)
      for(std::size_t operand1 = 0; operand1 < current_program_size; ++operand1)
      {
        // There is no point in applying a boolean binary operation if the
        // operands are identical.
        if(operand0 == operand1)
          continue;

        // Boolean binary operations are commutative, so there is no need
        // to have both orderings.
        if(operand0 > operand1)
          continue;

        irep_idt sel_id = id2string(function_identifier) + SELECTOR_SEPARATOR +
                          std::to_string(current_program_size) +
                          SELECTOR_SEPARATOR + BINARY_PREFIX +
                          std::to_string(binary_option_index) + SELECTOR_FLAG;

        bool_e_datat::instructiont::optiont &option =
          instruction.add_option(sel_id);
        option.operand0 = operand0;
        option.operand1 = operand1;
        option.operation = operation;

        if(operation == ID_equal || operation == ID_notequal)
          option.kind = bool_e_datat::instructiont::optiont::BINARY_PREDICATE;
        else
          option.kind = bool_e_datat::instructiont::optiont::BINARY;

        binary_option_index++;
      }
}

/// Creates a ternary if-then-else with the selector deciding which
/// expression shall be executed.
/// \param selector: Symbol deciding which part of the expression shall be
///   executed.
/// \param expr_true: Expression to execute if the selector is set to true.
/// \param expr_false: Expression to execute if the selector is set to
///   false.
/// \return: If-expression for the given parameters.
static if_exprt chain(
  const symbol_exprt &selector,
  const exprt &expr_true,
  const exprt &expr_false)
{
  return if_exprt{selector, expr_true, expr_false};
}

/// Adds a selector for the given parameter to the current result.
/// \param option: Option that includes a parameter.
/// \param arguments: Parameters of the synthesised expression.
/// \param [out] result_expr: Current result to which the option shall be
///   added.
static void chain_parameter(
  const bool_e_datat::instructiont::optiont &option,
  const std::vector<exprt> &arguments,
  exprt &result_expr)
{
  result_expr =
    chain(option.sel, arguments[option.parameter_number], result_expr);
}

/// Adds a selector for the given unary operation to the current result.
/// \param option: Option that includes a parameter.
/// \param results: Data structure holding the results of other instructions.
/// \param [out] result_expr: Current result to which the option shall be
///   added.
static void chain_unary(
  const bool_e_datat::instructiont::optiont &option,
  const std::vector<exprt> &results,
  exprt &result_expr)
{
  PRECONDITION(option.operand0 < results.size());
  const exprt &op0 = results[option.operand0];
  unary_exprt unary_expr(option.operation, op0, bool_typet{});
  result_expr = chain(option.sel, unary_expr, result_expr);
}

/// Adds a selector for the given binary operation to the current result.
/// \param option: Option that includes a parameter.
/// \param results: Data structure holding the results of other instructions.
/// \param [out] result_expr: Current result to which the option shall be
///   added.
static void chain_binary(
  const bool_e_datat::instructiont::optiont &option,
  const std::vector<exprt> &results,
  exprt &result_expr)
{
  PRECONDITION(option.operand0 < results.size());
  PRECONDITION(option.operand1 < results.size());

  const exprt &op0 = results[option.operand0];
  const exprt &op1 = results[option.operand1];
  binary_exprt binary_expr(option.operation, bool_typet{});
  binary_expr.op0() = op0;
  binary_expr.op1() = op1;

  result_expr = chain(option.sel, binary_expr, result_expr);
}

/// Adds a selector for the given binary predicate operation to the current
/// result.
/// \param option: Option that includes a parameter.
/// \param results: Data structure holding the results of other instructions.
/// \param [out] result_expr: Current result to which the option shall be
///   added.
static void chain_predicate(
  const bool_e_datat::instructiont::optiont &option,
  const std::vector<exprt> &results,
  exprt &result_expr)
{
  PRECONDITION(option.operand0 < results.size());
  PRECONDITION(option.operand1 < results.size());

  const exprt &op0 = results[option.operand0];
  const exprt &op1 = results[option.operand1];

  binary_exprt binary_expr{option.operation, bool_typet()};
  binary_expr.op0() = op0;
  binary_expr.op1() = op1;

  result_expr = chain(option.sel, binary_expr, result_expr);
}

bool_e_datat::instructiont::optiont::optiont()
  : parameter_number(0), kind(NONE), operand0(0), operand1(0), operand2(0)
{
}

bool_e_datat::instructiont::instructiont(std::size_t _pc) : pc(_pc)
{
}

bool_e_datat::instructiont::optiont &
bool_e_datat::instructiont::add_option(const irep_idt &sel_identifier)
{
  options.push_back(optiont());
  options.back().sel = symbol_exprt(sel_identifier, bool_typet());
  return options.back();
}

bool_e_datat::bool_e_datat(
  const function_application_exprt &expression,
  const std::size_t program_size)
{
  function_symbol = expression.function();
  const irep_idt &identifier = function_symbol.get_identifier();

  const auto &arguments = expression.arguments();
  parameter_types.resize(arguments.size());
  for(std::size_t i = 0; i < parameter_types.size(); ++i)
    parameter_types[i] = arguments[i].type();

  PRECONDITION(is_bool_word_type());
  erase_unfitting_literals();

  instructions.reserve(program_size);
  for(std::size_t pc = 0; pc < program_size; ++pc)
  {
    instructions.push_back(instructiont{pc});
    auto &instruction = instructions[pc];

    // Constant (hard-wired default, not an option).
    const irep_idt const_val_id{id2string(identifier) + SELECTOR_SEPARATOR +
                                std::to_string(pc) + SELECTOR_SEPARATOR +
                                CONSTANT_TAG};
    instruction.constant_val = symbol_exprt{const_val_id, bool_typet{}};

    add_arguments_and_constants(
      instruction, pc, identifier, arguments.size() + literals.size());
    add_unary_options(instruction, pc, identifier);
    add_binary_options(instruction, pc, identifier);
  }
}

bool bool_e_datat::is_bool_word_type()
{
  for(const typet &t : parameter_types)
    if(t.id() != ID_bool)
      return false;
  return true;
}

exprt bool_e_datat::operator()(const argumentst &arguments)
{
  // Find out which instance this is.
  std::size_t instance_number = this->instance_number(arguments);

  std::vector<exprt> results;
  results.resize(instructions.size(), nil_exprt{});

  constraints.clear();

  const irep_idt &identifier = function_symbol.get_identifier();

  for(std::size_t pc = 0; pc < instructions.size(); ++pc)
  {
    argumentst args_with_consts(arguments);
    copy(begin(literals), end(literals), back_inserter(args_with_consts));
    exprt c = instructions[pc].constraint(args_with_consts, results);

    // Results vary by instance.
    const irep_idt result_identifier{
      id2string(identifier) + SELECTOR_SEPARATOR + INSTANCE_PREFIX +
      std::to_string(instance_number) + SELECTOR_SEPARATOR + RESULT_TAG +
      SELECTOR_SEPARATOR + std::to_string(pc)};

    results[pc] = symbol_exprt{result_identifier, c.type()};
    constraints.push_back(equal_exprt(results[pc], c));
  }

  PRECONDITION(!results.empty());

  return results.back();
}

exprt bool_e_datat::instructiont::constraint(
  const std::vector<exprt> &arguments,
  const std::vector<exprt> &results)
{
  // Constant (last resort).
  exprt result_expr = constant_val;

  for(const bool_e_datat::instructiont::optiont &option : options)
  {
    switch(option.kind)
    {
    case bool_e_datat::instructiont::optiont::PARAMETER:
      chain_parameter(option, arguments, result_expr);
      break;
    case optiont::UNARY:
      chain_unary(option, results, result_expr);
      break;
    case bool_e_datat::instructiont::optiont::BINARY:
      chain_binary(option, results, result_expr);
      break;
    case bool_e_datat::instructiont::optiont::BINARY_PREDICATE:
      chain_predicate(option, results, result_expr);
      break;
    case bool_e_datat::instructiont::optiont::ITE:
    case bool_e_datat::instructiont::optiont::NONE:
      std::cout << "error: option kind: " << option.kind << std::endl;
      UNREACHABLE;
    }
  }

  return result_expr;
}

std::size_t bool_e_datat::instance_number(const argumentst &arguments)
{
  const auto res = instances.insert(
    std::pair<argumentst, std::size_t>(arguments, instances.size()));

  return res.first->second;
}

exprt bool_e_datat::get_function(
  const decision_proceduret &solver,
  bool constant_variables) const
{
  PRECONDITION(!instructions.empty());

  std::vector<exprt> results;
  results.resize(instructions.size(), nil_exprt());

  for(std::size_t pc = 0; pc < instructions.size(); ++pc)
  {
    const instructiont &instruction = instructions[pc];
    exprt &result = results[pc];
    result = nil_exprt{};

    // Go backwards through the options because we have built the ite from the
    // inside-out.
    for(auto o_it = instruction.options.rbegin();
        result.is_nil() && o_it != instruction.options.rend();
        o_it++)
    {
      if(solver.get(o_it->sel).is_false())
        continue;
      switch(o_it->kind)
      {
      case instructiont::optiont::PARAMETER:
        result = decode_parameter(o_it->parameter_number);
        break;
      case instructiont::optiont::UNARY:
        result = decode_unary(*o_it, results);
        break;
      case instructiont::optiont::BINARY:
        result = decode_binary(*o_it, results);
        break;
      case instructiont::optiont::BINARY_PREDICATE:
        result = decode_predicate(*o_it, results);
        break;
      case instructiont::optiont::ITE:
      case instructiont::optiont::NONE:
        UNREACHABLE;
      }
    }

    // Constant, this is the last resort when none of the selectors is true.
    if(result.is_nil())
    {
      if(constant_variables)
        result = instruction.constant_val;
      else
        result = solver.get(instruction.constant_val);
    }
  }

  return results.back();
}

void bool_e_datat::erase_unfitting_literals()
{
  for(auto it(begin(literals)); it != end(literals);)
    if(it->type().id() != ID_bool)
      it = literals.erase(it);
    else
      ++it;
}

exprt bool_e_datat::decode_parameter(const size_t parameter_number) const
{
  const size_t num_params = parameter_types.size();
  if(parameter_number < num_params)
  {
    const irep_idt p_identifier{DECODED_PARAMETER_PREFIX +
                                std::to_string(parameter_number)};
    return symbol_exprt{p_identifier, parameter_types[parameter_number]};
  }
  else // Constant.
  {
    const size_t const_index = parameter_number - num_params;
    return *next(begin(literals), const_index);
  }
}

exprt bool_e_datat::decode_unary(
  const bool_e_datat::instructiont::optiont option,
  const std::vector<exprt> results) const
{
  PRECONDITION(option.operand0 < results.size());
  exprt op0 = results[option.operand0];
  return unary_exprt{option.operation, op0, bool_typet{}};
}

exprt bool_e_datat::decode_binary(
  const bool_e_datat::instructiont::optiont option,
  const std::vector<exprt> results) const
{
  PRECONDITION(option.operand0 < results.size());
  PRECONDITION(option.operand1 < results.size());

  exprt op0{results[option.operand0]};
  exprt op1{results[option.operand1]};
  return binary_exprt{op0, option.operation, op1, bool_typet{}};
}

exprt bool_e_datat::decode_predicate(
  const bool_e_datat::instructiont::optiont option,
  const std::vector<exprt> results) const
{
  PRECONDITION(option.operand0 < results.size());
  PRECONDITION(option.operand1 < results.size());

  return binary_exprt{results[option.operand0],
                      option.operation,
                      results[option.operand1],
                      bool_typet{}};
}

exprt bool_e_datat::decode_ternary(
  const bool_e_datat::instructiont::optiont option,
  const std::vector<exprt> results) const
{
  PRECONDITION(option.operand0 < results.size());
  PRECONDITION(option.operand1 < results.size());
  PRECONDITION(option.operand2 < results.size());

  return if_exprt{results[option.operand0],
                  results[option.operand1],
                  results[option.operand2]};
}

exprt bool_synth_encodingt::operator()(const exprt &expr)
{
  if(expr.id() == ID_function_application)
  {
    function_application_exprt function_expr =
      to_function_application_expr(expr);

    // Apply recursively to arguments.
    for(exprt &op : function_expr.arguments())
      op = (*this)(op);

    auto map_it = e_data_per_function.find(function_expr.function());
    if(map_it == end(e_data_per_function))
    {
      bool_e_datat new_data{function_expr, program_size};
      new_data.literals = literals;
      map_it = e_data_per_function
                 .emplace(function_expr.function(), std::move(new_data))
                 .first;
    }
    bool_e_datat &e_data = map_it->second;

    exprt final_result = e_data(function_expr.arguments());

    for(const exprt &c : e_data.constraints)
      constraints.push_back(c);
    return final_result;
  }
  else if(expr.id() == ID_symbol)
  {
    // Add the suffix.
    symbol_exprt tmp = to_symbol_expr(expr);
    tmp.set_identifier(id2string(tmp.get_identifier()) + suffix);
    return std::move(tmp);
  }
  else if(expr.id() == ID_nondet_symbol)
  {
    // Add the suffix.
    nondet_symbol_exprt tmp = to_nondet_symbol_expr(expr);
    irep_idt identifier = tmp.get_identifier();
    tmp.set_identifier(id2string(identifier) + suffix);
    return std::move(tmp);
  }
  else
  {
    exprt tmp = expr;

    // Recursive call.
    for(exprt &op : tmp.operands())
      op = (*this)(op);

    return tmp;
  }
}

solutiont
bool_synth_encodingt::get_solution(const decision_proceduret &solver) const
{
  solutiont result;

  for(const std::pair<const symbol_exprt, bool_e_datat> &it :
      e_data_per_function)
  {
    result.functions[it.first] = it.second.get_function(solver, false);
    result.s_functions[it.first] = it.second.get_function(solver, true);
  }
  return result;
}

void bool_synth_encodingt::clear()
{
  e_data_per_function.clear();
  constraints.clear();
}
