/*******************************************************************\

 Module: Fastsynth Boolean Synth Encoding

 Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

#include "bool_synth_encoding.h"

#include <util/bv_arithmetic.h>
#include <util/config.h>
#include <util/std_types.h>

#include <algorithm>
#include <iterator>

/// Used to indicate that the ID is a selector.
#define SELECTOR_FLAG "sel"

/// Separates function name, selector ID and other tags from each other.
#define SELECTOR_SEPARATOR '_'

/// Prefix of a nullary instruction, used in selector names.
#define NULLARY_PREFIX 'o'

/// Prefix of a unary operation, used in selector names.
#define UNARY_PREFIX 'u'

/// Prefix of a constant, used in selector names.
#define CONSTANT_TAG "cval"

/// Prefix of a decoded parameter, used when generating solutions.
#define DECODED_PARAMETER_PREFIX "synth::parameter"

/// Prefix of different instances, used in results.
#define INSTANCE_PREFIX "inst"

/// Tag to indicate that the affected ID belongs to a result.
#define RESULT_TAG "result"

/// Names of all supported unary instructions.
static const std::vector<irep_idt> unary_instructions = {
  ID_statement_list_and,
  ID_statement_list_and_not,
  ID_statement_list_or,
  ID_statement_list_or_not,
  ID_statement_list_xor,
  ID_statement_list_xor_not,
};

/// Names of all supported nullary instructions.
static const std::vector<irep_idt> nullary_instructions = {
  ID_statement_list_not,
};

void bool_synth_encodingt::clear()
{
  e_data_per_function.clear();
  constraints.clear();
}

/// Either constructs a binary expression for the given ID in the case that
/// the previous result is not nil or simply returns the operand of the
/// instruction.
/// \param target_expression: ID of the wanted binary expression.
/// \param prev_result: Operand constructed by previous instructions. Can be
///   nil to mark the beginning of a new bit string.
/// \param op: Operand of the instruction to convert.
/// \return Binary expression or operand of the instruction.
static exprt convert_boolean_instruction(
  const irep_idt &target_expression,
  const exprt &prev_result,
  const exprt &op)
{
  if(prev_result.is_nil())
    return op;
  else
    return binary_exprt{prev_result, target_expression, op};
}

/// Converts the given option in its expression form based on the result of
/// previous instructions.
/// \param option: Instruction to convert.
/// \param prev_result: Operand constructed by previous instructions. Can be
///   nil to mark the beginning of a new bit string.
/// \param operand: Operand of the instruction to convert.
/// \return Binary expression or operand of the instruction if this is a new
///   bit string.
static exprt convert_unary_to_exp(
  const bool_e_datat::instructiont::optiont &option,
  const exprt &prev_result,
  const exprt &operand)
{
  if(ID_statement_list_and == option.operation)
    return convert_boolean_instruction(ID_and, prev_result, operand);
  else if(ID_statement_list_and_not == option.operation)
    return convert_boolean_instruction(ID_and, prev_result, not_exprt{operand});
  else if(ID_statement_list_or == option.operation)
    return convert_boolean_instruction(ID_or, prev_result, operand);
  else if(ID_statement_list_or_not == option.operation)
    return convert_boolean_instruction(ID_or, prev_result, not_exprt{operand});
  else if(ID_statement_list_xor == option.operation)
    return convert_boolean_instruction(ID_xor, prev_result, operand);
  else if(ID_statement_list_xor_not == option.operation)
    return convert_boolean_instruction(ID_xor, prev_result, not_exprt{operand});
  else
    UNREACHABLE;
}

/// Converts the given option in its expression form based on the result of
/// previous instructions.
/// \param option: Instruction to convert.
/// \param operand: Operand constructed by previous instructions. Can be
///   nil to mark the beginning of a new bit string.
/// \return Unary expression or false_exprt if this is a new bit string.
static exprt convert_nullary_to_exp(
  const bool_e_datat::instructiont::optiont &option,
  const exprt &operand)
{
  if(ID_statement_list_not == option.operation)
  {
    if(operand.is_nil())
      return false_exprt{};
    else
      return not_exprt{operand};
  }
  else
    UNREACHABLE;
}

symbol_exprt bool_e_datat::decode_parameter(const size_t parameter_number) const
{
  PRECONDITION(parameter_number < function_arguments.size());
  const irep_idt p_identifier{DECODED_PARAMETER_PREFIX +
                              std::to_string(parameter_number)};
  return symbol_exprt{p_identifier,
                      function_arguments[parameter_number].type()};
}

exprt bool_e_datat::get_function(const decision_proceduret &solver) const
{
  PRECONDITION(!instructions.empty());

  exprt rlo_bit = nil_exprt{};

  for(std::size_t pc = 0; pc < instructions.size(); ++pc)
  {
    const instructiont &instruction = instructions[pc];
    instructiont::optiont option{};

    // Go backwards through the options because we have built the constraints
    // from the inside-out. Break if a selector is true or the default case has
    // been reached.
    for(auto o_it = instruction.options.rbegin();
        o_it != instruction.options.rend();
        ++o_it)
      if(
        o_it->sel.get(ID_identifier) == ID_nil ||
        solver.get(o_it->sel).is_true())
      {
        option = *o_it;
        break;
      }

    switch(option.kind)
    {
    case instructiont::optiont::NULLARY:
      rlo_bit = convert_nullary_to_exp(option, rlo_bit);
      break;
    case instructiont::optiont::UNARY:
      rlo_bit =
        convert_unary_to_exp(option, rlo_bit, decode_parameter(option.operand));
      break;
    case instructiont::optiont::NONE:
      UNREACHABLE;
    }
  }
  return rlo_bit;
}

solutiont
bool_synth_encodingt::get_solution(const decision_proceduret &solver) const
{
  solutiont result;
  for(const std::pair<const symbol_exprt, bool_e_datat> &it :
      e_data_per_function)
  {
    exprt function{it.second.get_function(solver)};
    result.functions[it.first] = function;
    result.s_functions[it.first] = function;
  }
  return result;
}

/// Creates a ternary if-then-else with the selector deciding which
/// expression shall be executed.
/// \param selector: Symbol deciding which part of the expression shall be
///   executed.
/// \param expr_true: Expression to execute if the selector is set to true.
/// \param expr_false: Expression to execute if the selector is set to
///   false.
/// \return If-expression for the given parameters.
static if_exprt chain(
  const symbol_exprt &selector,
  const exprt &expr_true,
  const exprt &expr_false)
{
  return if_exprt{selector, expr_true, expr_false};
}

exprt bool_e_datat::instructiont::constraint(
  const argumentst &arguments,
  const exprt &prev_result)
{
  std::vector<exprt> converted_options;
  converted_options.reserve(options.size());
  for(const instructiont::optiont option : options)
  {
    exprt converted{};
    switch(option.kind)
    {
    case bool_e_datat::instructiont::optiont::NULLARY:
      converted = convert_nullary_to_exp(option, prev_result);
      converted_options.push_back(std::move(converted));
      break;
    case optiont::UNARY:
      converted =
        convert_unary_to_exp(option, prev_result, arguments[option.operand]);
      converted_options.push_back(std::move(converted));
      break;
    case bool_e_datat::instructiont::optiont::NONE:
      UNREACHABLE;
    }
  }

  // Use first option as the default case.
  exprt result_expr{converted_options.front()};

  for(std::size_t i = 1; i < options.size(); ++i)
    result_expr = chain(options[i].sel, converted_options[i], result_expr);

  return result_expr;
}

std::size_t bool_e_datat::instance_number(const argumentst &arguments)
{
  const auto res = instances.insert(
    std::pair<argumentst, std::size_t>(arguments, instances.size()));

  return res.first->second;
}

exprt bool_e_datat::operator()(const argumentst &arguments)
{
  // Find out which instance this is.
  const std::size_t instance_number = this->instance_number(arguments);
  const irep_idt &identifier = function_symbol.get_identifier();
  std::vector<exprt> results;
  results.resize(instructions.size(), nil_exprt{});
  exprt prev_result = nil_exprt{};

  constraints.clear();

  for(std::size_t pc = 0; pc < instructions.size(); ++pc)
  {
    exprt c = instructions[pc].constraint(arguments, prev_result);

    // Results vary by instance.
    const irep_idt result_identifier{
      id2string(identifier) + SELECTOR_SEPARATOR + INSTANCE_PREFIX +
      std::to_string(instance_number) + SELECTOR_SEPARATOR + RESULT_TAG +
      SELECTOR_SEPARATOR + std::to_string(pc)};

    prev_result = symbol_exprt{result_identifier, c.type()};
    results[pc] = prev_result;
    constraints.push_back(equal_exprt(results[pc], c));
  }

  PRECONDITION(!results.empty());
  return results.back();
}

/// Adds all unary instruction options supported by the encoding to the given
/// instruction.
/// \param [out] instruction: Instruction to add the options to.
/// \param operand_pool: Total number of possible operands. When building an
///   option, its operand is referenced by a number between zero and this
///   parameter. The reference gets replaced during the decoding process.
/// \param function_identifier: Name of the synthesised expression.
static void add_unary_instructions(
  bool_e_datat::instructiont &instruction,
  const size_t &operand_pool,
  const irep_idt &function_identifier)
{
  std::size_t unary_instruction_index = 0;

  for(const irep_idt operation : unary_instructions)
    for(std::size_t operand = 0; operand < operand_pool; ++operand)
    {
      const irep_idt sel_id{
        id2string(function_identifier) + SELECTOR_SEPARATOR +
        std::to_string(instruction.pc) + SELECTOR_SEPARATOR + UNARY_PREFIX +
        std::to_string(unary_instruction_index) + SELECTOR_FLAG};

      bool_e_datat::instructiont::optiont &option =
        instruction.add_option(sel_id);
      option.operand = operand;
      option.operation = operation;
      option.kind = bool_e_datat::instructiont::optiont::UNARY;
      ++unary_instruction_index;
    }
}

bool_e_datat::instructiont::optiont::optiont() : kind(NONE), operand(0)
{
}

bool_e_datat::instructiont::optiont &
bool_e_datat::instructiont::add_option(const irep_idt &sel_identifier)
{
  options.push_back(optiont{});
  options.back().sel = symbol_exprt(sel_identifier, bool_typet());
  return options.back();
}

/// Adds all instruction options without an operand to the given instruction.
/// Note: The first option servers as the default case for the ITE later and
/// and thus contains no selector.
/// \param [out] instruction: Instruction to add the options to.
/// \param function_identifier: Name of the synthesised expression.
static void add_nullary_instructions(
  bool_e_datat::instructiont &instruction,
  const irep_idt &function_identifier)
{
  auto opt_it = begin(nullary_instructions);

  // Add the default case.
  bool_e_datat::instructiont::optiont &option = instruction.add_option(ID_nil);
  option.operation = *opt_it;
  option.kind = bool_e_datat::instructiont::optiont::NULLARY;

  ++opt_it;

  size_t nullary_option_index = 0;
  for(; opt_it != end(nullary_instructions); ++opt_it)
  {
    const irep_idt sel_id{id2string(function_identifier) + SELECTOR_SEPARATOR +
                          std::to_string(instruction.pc) + SELECTOR_SEPARATOR +
                          NULLARY_PREFIX +
                          std::to_string(nullary_option_index) + SELECTOR_FLAG};

    bool_e_datat::instructiont::optiont &option =
      instruction.add_option(sel_id);
    option.operation = *opt_it;
    option.kind = bool_e_datat::instructiont::optiont::NULLARY;
    ++nullary_option_index;
  }
}

bool_e_datat::instructiont::instructiont(std::size_t pc) : pc(pc)
{
}

void bool_e_datat::erase_unfitting_literals()
{
  for(auto it(begin(literals)); it != end(literals);)
    if(it->type().id() != ID_bool)
      it = literals.erase(it);
    else
      ++it;
}

bool bool_e_datat::is_bool_word_type()
{
  auto it = find_if(
    begin(function_arguments), end(function_arguments), [](const exprt &arg) {
      return arg.type().id() != ID_bool;
    });
  return it == end(function_arguments);
}

bool_e_datat::bool_e_datat(
  const function_application_exprt &expression,
  const std::size_t program_size)
  : function_arguments(expression.arguments())
{
  function_symbol = expression.function();
  const irep_idt &identifier = function_symbol.get_identifier();

  PRECONDITION(is_bool_word_type());
  erase_unfitting_literals();

  instructions.reserve(program_size);
  for(std::size_t pc = 0; pc < program_size; ++pc)
  {
    instructions.push_back(instructiont{pc});
    auto &instruction = instructions[pc];

    add_nullary_instructions(instruction, identifier);
    add_unary_instructions(instruction, function_arguments.size(), identifier);
  }
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
  else if(expr.id() == ID_nondet_symbol || expr.id() == ID_symbol)
  {
    // Add the suffix.
    exprt tmp{expr};
    irep_idt identifier = id2string(tmp.get(ID_identifier)) + suffix;
    tmp.set(ID_identifier, identifier);
    return tmp;
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
