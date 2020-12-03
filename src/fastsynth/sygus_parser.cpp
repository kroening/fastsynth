#include "sygus_parser.h"

#include <util/bv_arithmetic.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/replace_symbol.h>
#include <util/arith_tools.h>

#include <cctype>
#include <cassert>
#include <fstream>

void sygus_parsert::command_sequence()
{
  while(smt2_tokenizer.next_token()==smt2_tokenizert::OPEN)
  {
    if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
      throw error("expected symbol as command");

    command(smt2_tokenizer.get_buffer());

    switch(smt2_tokenizer.next_token())
    {
    case smt2_tokenizert::END_OF_FILE:
      throw error("expected closing parenthesis at end of command, but got EOF");

    case smt2_tokenizert::CLOSE:
      // what we expect
      break;

    case smt2_tokenizert::NONE:
    case smt2_tokenizert::STRING_LITERAL:
    case smt2_tokenizert::NUMERAL:
    case smt2_tokenizert::SYMBOL:
    case smt2_tokenizert::KEYWORD:
    case smt2_tokenizert::OPEN:
      throw error("expected end of command");
    }
  }

  if(smt2_tokenizer.peek()!=smt2_tokenizert::END_OF_FILE)
    throw error("unexpected token in command sequence");
}

void sygus_parsert::ignore_command()
{
  std::size_t parentheses=0;
  while(true)
  {
    switch(smt2_tokenizer.peek())
    {
    case smt2_tokenizert::OPEN:
      smt2_tokenizer.next_token();
      parentheses++;
      break;

    case smt2_tokenizert::CLOSE:
      if(parentheses==0)
        return; // done

      smt2_tokenizer.next_token();
      parentheses--;
      break;

    case smt2_tokenizert::END_OF_FILE:
      throw error("unexpected EOF in command");

    case smt2_tokenizert::NONE:
    case smt2_tokenizert::STRING_LITERAL:
    case smt2_tokenizert::NUMERAL:
    case smt2_tokenizert::SYMBOL:
    case smt2_tokenizert::KEYWORD:
      smt2_tokenizer.next_token();
    }
  }
}
exprt::operandst sygus_parsert::operands()
{
  exprt::operandst result;

  while(smt2_tokenizer.peek()!=smt2_tokenizert::CLOSE)
    result.push_back(expression());

  smt2_tokenizer.next_token(); // eat the ')'

  return result;
}

exprt sygus_parsert::let_expression(bool first_in_chain)
{
  let_counter++;

  if(smt2_tokenizer.peek()!=smt2_tokenizert::OPEN && !first_in_chain)
  {
    // no need for chaining, single let exprt.
    auto ops=operands();

    if(ops.size()!=3)
      throw error("let expression has three components");
    else if(ops[0].id()!=ID_symbol)
      throw error("expected symbol in let expression");
    else
      return let_exprt(to_symbol_expr(ops[0]), ops[1], ops[2]);
  }
  else
  {
    if(smt2_tokenizer.peek()==smt2_tokenizert::OPEN && first_in_chain)
    {
      smt2_tokenizer.next_token(); // eat the '(' that starts the bindings list
    }

    smt2_tokenizer.next_token(); // eat the '(' that starts the next binding

    exprt symbol_expr, value_expr, where_expr;

    // get the symbol that is bound
    if(smt2_tokenizer.next_token()==smt2_tokenizert::SYMBOL)
    {
      std::string tmp_buffer;
      symbol_expr = symbol_exprt(tmp_buffer, sort());
    }
    else
      throw error("expected symbol in let expression");

    // get value
    value_expr = expression();
    smt2_tokenizer.next_token(); // eat the ')' that closes this binding

    // now rename op0 -- this really happens at the very
    // end of the let, but that's hard with recursion
    irep_idt old_id=to_symbol_expr(symbol_expr).get_identifier();
    irep_idt new_id=id2string(old_id)+
                    '#'+std::to_string(id_counter++)+
                    'L'+std::to_string(let_counter++);

    to_symbol_expr(symbol_expr).set_identifier(new_id);
    let_variable_map[new_id]=value_expr.type();
    full_let_variable_map[new_id]=value_expr.type();
    renaming_map[old_id]=new_id;

    if(smt2_tokenizer.peek()!=smt2_tokenizert::CLOSE) // we are still in a chain of bindings
    {
      // get op2
      where_expr = let_expression(false);
    }
    else
    {
      // we are at the end of the chain
      smt2_tokenizer.next_token(); // eat the ')' that closes the bindings list

      if(smt2_tokenizer.peek()!=smt2_tokenizert::OPEN)
        throw error("let expects where here");

      where_expr = expression();
      smt2_tokenizer.next_token(); // eat the final ')' that closes the let exprt
    }

    // don't rename any longer
    renaming_map.erase(old_id);
    let_variable_map.clear();

    return let_exprt(to_symbol_expr(symbol_expr), value_expr, where_expr);
  }
}

exprt sygus_parsert::function_application(
  const irep_idt &identifier,
  const exprt::operandst &op)
{
  const auto &f = function_map[identifier];

  function_application_exprt result(
    symbol_exprt(identifier, f.type),
    op,
    f.type.codomain());

  // check the arguments
  if(op.size()!=f.type.domain().size())
    throw error("wrong number of arguments for function");

  for(std::size_t i=0; i<op.size(); i++)
  {
    if(op[i].type() != f.type.domain()[i])
      throw error("wrong type for arguments for function");
  }

  return std::move(result);
}

void sygus_parsert::fix_ite_operation_result_type(if_exprt &expr)
{
  if(expr.cond().id()!=ID_bool)
    expr.cond().type()=bool_typet();

  if(expr.true_case().type()!=expr.false_case().type())
  {
   // default type is unsigned bitvector
    if(expr.op1().type().id()==ID_unsignedbv)
      expr.op2().type()=expr.op1().type();
    else if(expr.op1().type().id()==ID_unsignedbv)
      expr.op1().type()=expr.op2().type();
    else if(expr.op1().type().id()==ID_signedbv)
    {
      unsignedbv_typet type(to_signedbv_type(expr.op1().type()).get_width());
      expr.op1().type()=type;
      expr.op2().type()=type;
    }
    else if(expr.op2().type().id()==ID_signedbv)
    {
      unsignedbv_typet type(to_signedbv_type(expr.op2().type()).get_width());
      expr.op1().type()=type;
      expr.op2().type()=type;
    }

    // throw error if still mismatching. Could be because bitvector widths are different
    if(expr.true_case().type()!=expr.false_case().type())
      throw error("mismatching types for ite operand");
  }

  expr.type()=expr.true_case().type();
}

void sygus_parsert::fix_binary_operation_operand_types(exprt &expr)
{
  // TODO: deal with different widths of bitvector
  if(expr.operands().size()!=2)
    throw error("two operands expected for binary operation");

  if(expr.op0().type()!=expr.op1().type())
  {
    // default type is unsigned bitvector
    if(expr.op0().type().id()==ID_unsignedbv)
      expr.op1().type()=expr.op0().type();
    else if(expr.op1().type().id()==ID_unsignedbv)
      expr.op0().type()=expr.op1().type();
    else if(expr.op0().type().id()==ID_signedbv)
    {
      unsignedbv_typet type(to_signedbv_type(expr.op0().type()).get_width());
      expr.op0().type()=type;
      expr.op1().type()=type;
    }
    else if(expr.op1().type().id()==ID_signedbv)
    {
      unsignedbv_typet type(to_signedbv_type(expr.op1().type()).get_width());
      expr.op0().type()=type;
      expr.op1().type()=type;
    }

    // throw error if still mismatching. Could be because bitvector widths are different
    if(expr.op0().type()!=expr.op1().type())
      throw error("mismatching types for binary operator");
  }
}


exprt sygus_parsert::cast_bv_to_signed(exprt &expr)
{
  if(expr.type().id()==ID_signedbv) // no need to cast
    return expr;

  if(expr.type().id()!=ID_unsignedbv)
    throw error("expected unsigned bitvector");

 signedbv_typet signed_type(to_unsignedbv_type(expr.type()).get_width());
 return typecast_exprt(expr, signed_type);
}

exprt sygus_parsert::cast_bv_to_unsigned(exprt &expr)
{
  if(expr.type().id()==ID_unsignedbv) // no need to cast
    return expr;

  if(expr.type().id()!=ID_signedbv)
    throw error("expected signed bitvector");

  unsignedbv_typet unsigned_type(to_signedbv_type(expr.type()).get_width());
  return typecast_exprt(expr, unsigned_type);
}

static bool is_negative_numeral(const std::string &s)
{
  if(s.size()>=2 && s[0]=='-')
  {
    for(std::size_t i=1; i<s.size(); i++)
      if(!isdigit(s[i]))
        return false;

    return true;
  }
  else
    return false;
}

exprt sygus_parsert::expression()
{
  switch(smt2_tokenizer.next_token())
  {
  case smt2_tokenizert::SYMBOL:
    // sugys allows negative numerals "-1",
    // which are a smt2_tokenizert::SYMBOL in SMT-LIB2
    if(is_negative_numeral(smt2_tokenizer.get_buffer()))
    {
      return constant_exprt(smt2_tokenizer.get_buffer(), integer_typet());
    }
    else
    {
      // hash it
      irep_idt identifier=smt2_tokenizer.get_buffer();

      // renamed?
      const auto r_it=renaming_map.find(identifier);
      if(r_it!=renaming_map.end())
        identifier=r_it->second;

      if(identifier==ID_true)
        return true_exprt();
      else if(identifier==ID_false)
        return false_exprt();
      else if(local_variable_map.find(identifier)!=
              local_variable_map.end())
      {
        // search local variable map first, we clear the local variable map
        // as soon as we are done parsing the function body
        return symbol_exprt(identifier, local_variable_map[identifier]);
      }
      else if(variable_map.find(identifier)!=
              variable_map.end())
      {
        return symbol_exprt(identifier, variable_map[identifier]);
      }
      else if(let_variable_map.find(identifier)!=
          let_variable_map.end())
      {
        // search let variables, we clear let variables when done with parsing let
        return symbol_exprt(identifier, let_variable_map[identifier]);
      }
      else if(function_map.find(identifier)!=
              function_map.end())
      {
        return function_application(identifier, exprt::operandst());
      }
      else
        throw error() << "unknown symbol `" << smt2_tokenizer.get_buffer() << '\'';
    }

  case smt2_tokenizert::NUMERAL:
    {
      const auto &buffer = smt2_tokenizer.get_buffer();
      if(buffer.size()>=2 && buffer[0]=='#' && buffer[1]=='x')
      {
        mp_integer value=
          string2integer(std::string(buffer, 2, std::string::npos), 16);
        const std::size_t width = 4*(buffer.length() - 2);
        CHECK_RETURN(width!=0 && width%4==0);
        unsignedbv_typet type(width);
        return from_integer(value, type);
      }
      else if(buffer.size()>=2 && buffer[0]=='#' && buffer[1]=='b')
      {
        mp_integer value=
          string2integer(std::string(buffer, 2, std::string::npos), 2);
        const std::size_t width = buffer.size() - 2;
        CHECK_RETURN(width!=0 && width%2==0);
        unsignedbv_typet type(width);
        return from_integer(value, type);
      }
      else
      {
        return constant_exprt(buffer, integer_typet());
      }
    }

  case smt2_tokenizert::OPEN:
    if(smt2_tokenizer.next_token()==smt2_tokenizert::SYMBOL)
    {
      // hash it
      const irep_idt id=smt2_tokenizer.get_buffer();

      if(id==ID_let)
      {
        // bool indicates first in chain
        return let_expression(true);
      }

      auto op=operands();

      if(id==ID_and)
      {
        and_exprt result;
        result.operands()=op;
        return std::move(result);
      }
      else if(id==ID_or)
      {
        or_exprt result;
        result.operands()=op;
        return std::move(result);
      }
      else if(id==ID_xor)
      {
        notequal_exprt result(op.front(), op.back());
        return std::move(result);
      }
      else if(id==ID_not)
      {
        not_exprt result;
        result.operands()=op;
        return std::move(result);
      }
      else if(id=="=")
      {
        equal_exprt result(op.front(), op.back());
        fix_binary_operation_operand_types(result);
        result.type()=bool_typet();
        return std::move(result);
      }
      else if(id=="<=" || id=="bvule" || id=="bvsle")
      {
        binary_predicate_exprt result(ID_le);
        result.operands()=op;

        fix_binary_operation_operand_types(result);
        result.type()=bool_typet();

        if(id=="bvsle")
        {
          result.op0()=cast_bv_to_signed(result.op0());
          result.op1()=cast_bv_to_signed(result.op1());
        }
        return std::move(result);
      }
      else if(id==">=" || id=="bvuge" || id=="bvsge")
      {
        binary_predicate_exprt result(ID_ge);
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=bool_typet();

        if(id=="bvsge")
        {
          result.op0()=cast_bv_to_signed(result.op0());
          result.op1()=cast_bv_to_signed(result.op1());
        }

        return std::move(result);
      }
      else if(id=="<" || id=="bvult" || id=="bvslt")
      {
        binary_predicate_exprt result(ID_lt);
        result.operands()=op;

        fix_binary_operation_operand_types(result);
        result.type()=bool_typet();

        if(id=="bvslt")
        {
          result.op0()=cast_bv_to_signed(result.op0());
          result.op1()=cast_bv_to_signed(result.op1());
        }
        return std::move(result);
      }
      else if(id==">" || id=="bvugt" || id=="bvsgt")
      {
        binary_predicate_exprt result(ID_gt);
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=bool_typet();

        if(id=="bvsgt")
        {
          result.op0()=cast_bv_to_signed(result.op0());
          result.op1()=cast_bv_to_signed(result.op1());
        }
        return std::move(result);
      }
      else if(id=="bvashr")
      {
        if(op.size()!=2)
          throw error("bit shift must have 2 operands");

        ashr_exprt result(op[0], op[1]);
        result.type()=op[0].type();
        return std::move(result);
      }
      else if(id=="bvlshr" || id=="bvshr")
      {
        if(op.size()!=2)
          throw error("bit shift must have two operands");

        lshr_exprt result(op[0], op[1]);
        result.type()=op[0].type();
        return std::move(result);
      }
      else if(id=="bvlshr" || id=="bvashl" || id=="bvshl")
      {
        if(op.size()!=2)
          throw error("bit shift must have two operands");

        shl_exprt result(op[0], op[1]);
        result.type()=op[0].type();
        return std::move(result);
      }
      else if(id=="bvand")
      {
        bitand_exprt result(std::move(op.front()), std::move(op.back()));
        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();

        return std::move(result);
      }
      else if(id=="bvor")
      {
        bitor_exprt result(std::move(op.front()), std::move(op.back()));
        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();
        return std::move(result);
      }
      else if(id=="bvxor")
      {
        bitxor_exprt result(std::move(op.front()), std::move(op.back()));
        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();
        return std::move(result);
      }
      else if(id=="bvnot")
      {
        return bitnot_exprt(op.front());
      }
      else if(id=="bvneg")
      {
        return unary_minus_exprt(op.front());
      }
      else if(id=="bvadd" || id=="+")
      {
        typet type(op.front().type());
        plus_exprt result(move(op), std::move(type));
        fix_binary_operation_operand_types(result);
        return std::move(result);
      }
      else if(id=="bvsub" || id=="-")
      {
        if(op.size() == 1u)
          return unary_minus_exprt(op.front());

        minus_exprt result(std::move(op.front()), std::move(op.back()));
        fix_binary_operation_operand_types(result);
        return std::move(result);
      }
      else if(id=="bvmul" || id=="*")
      {
        mult_exprt result(std::move(op.front()), std::move(op.back()));
        fix_binary_operation_operand_types(result);
        return std::move(result);
      }
      else if(id=="bvudiv")
      {
        div_exprt div_res(std::move(op.front()), std::move(op.back()));
        fix_binary_operation_operand_types(div_res);

        // is op1 equal to zero? If it is, division returns max value of op0
        equal_exprt op_divbyzero(
          div_res.op1(), from_integer(0, div_res.op1().type()));

        bv_spect spec(div_res.op0().type());
        if_exprt result(
            op_divbyzero,
            from_integer(spec.max_value(), div_res.op0().type()),
            div_res);

        result.type()=div_res.type();
        return std::move(result);
      }
      else if(id == "bvsdiv")
      {
        div_exprt div_res(std::move(op.front()), std::move(op.back()));
        fix_binary_operation_operand_types(div_res);

        div_res.op0() = cast_bv_to_signed(div_res.op0());
        div_res.op1() = cast_bv_to_signed(div_res.op1());
        exprt signed_res = cast_bv_to_unsigned(div_res);

        // is op1 equal to zero? If it is, division returns max value of op0
        equal_exprt op_divbyzero(signed_res.op1(), from_integer(0, signed_res.op1().type()));

        bv_spect spec(signed_res.op0().type());
        if_exprt result(op_divbyzero,
            from_integer(spec.max_value(), signed_res.op0().type()), signed_res);

        result.type() = signed_res.type();
        return std::move(result);
      }
      else if(id=="/" || id=="div")
      {
        div_exprt result(std::move(op.front()), std::move(op.back()));
        fix_binary_operation_operand_types(result);
        return std::move(result);
      }
      else if(id=="bvsrem" || id=="bvurem" || id=="%")
      {
        mod_exprt result(std::move(op.front()), std::move(op.back()));
        fix_binary_operation_operand_types(result);

        if(id=="bvsrem")
        {
          result.op0()=cast_bv_to_signed(result.op0());
          result.op1()=cast_bv_to_signed(result.op1());
          return cast_bv_to_unsigned(result);
        }

        return std::move(result);
      }
      else if(id=="ite")
      {
        if(op.size()!=3)
          throw error("ITE must have three operands");
        if_exprt result(op[0], op[1], op[2]);
        fix_ite_operation_result_type(result);
        return std::move(result);
      }
      else if(id=="=>" || id=="implies")
      {
        implies_exprt result(std::move(op.front()), std::move(op.back()));
        return std::move(result);
      }
      else
      {
        if(function_map.count(id)!=0)
        {
          return function_application(id, op);
        }
        else if(local_variable_map.find(id)!=local_variable_map.end())
        {
          symbol_exprt result(id, local_variable_map[id]);
          return std::move(result);
        }
        else if(let_variable_map.find(id)!=let_variable_map.end())
        {
          symbol_exprt result(id, let_variable_map[id]);
          return std::move(result);
        }
        else if(variable_map.find(id)!=variable_map.end())
        {
          symbol_exprt result(id, variable_map[id]);
          return std::move(result);
        }
        else
          throw error("use of undeclared symbol or function");
      }
    }
    else
      throw error("expected symbol after '(' in an expression");

  case smt2_tokenizert::END_OF_FILE:
    throw error("EOF in an expression");

  case smt2_tokenizert::NONE:
  case smt2_tokenizert::STRING_LITERAL:
  case smt2_tokenizert::KEYWORD:
  case smt2_tokenizert::CLOSE:
  default:
    throw error("unexpected token in an expression");
  }
}

sygus_parsert::signature_with_parameter_idst sygus_parsert::function_signature()
{
  if(smt2_tokenizer.next_token()!=smt2_tokenizert::OPEN)
    throw error("expected '(' at beginning of signature");

  mathematical_function_typet::domaint domain;
  std::vector<irep_idt> parameter_ids;

  while(smt2_tokenizer.peek()!=smt2_tokenizert::CLOSE)
  {
    if(smt2_tokenizer.next_token()!=smt2_tokenizert::OPEN)
      throw error("expected '(' at beginning of parameter");

    if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
      throw error("expected symbol in parameter");

    const irep_idt id=smt2_tokenizer.get_buffer();

    const auto parameter_type=sort();
    domain.push_back(parameter_type);
    parameter_ids.push_back(id);
    local_variable_map[id]=parameter_type;

    if(smt2_tokenizer.next_token()!=smt2_tokenizert::CLOSE)
      throw error("expected ')' at end of parameter");
  }

  smt2_tokenizer.next_token(); // eat the ')'

  auto codomain = sort();

  auto type=mathematical_function_typet(domain, codomain);
  return signature_with_parameter_idst(type, parameter_ids);
}

void sygus_parsert::command(const std::string &c)
{
  if(c=="declare-var")
  {
    if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after declare-var");

    irep_idt id=smt2_tokenizer.get_buffer();

    if(variable_map.find(id)!=variable_map.end())
      throw error("variable declared twice");

    variable_map[id]=sort();
  }
  else if(c=="define-fun")
  {
    if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after define-fun");

    const irep_idt id=smt2_tokenizer.get_buffer();

    if(function_map.find(id)!=function_map.end())
      throw error("function declared twice");

    local_variable_map.clear();

    auto signature=function_signature();
    exprt body=expression();

    // check type of body
    if(signature.type.id() == ID_mathematical_function)
    {
      const auto &f_signature = to_mathematical_function_type(signature.type);
      if(body.type() != f_signature.codomain())
      {
        throw error()
          << "type mismatch in function definition: expected `"
          << f_signature.codomain().pretty() << "' but got `"
          << body.type().pretty() << '\'';
      }
    }
    else if(body.type() != signature.type)
    {
      throw error()
        << "type mismatch in function definition: expected `"
        << signature.type.pretty() << "' but got `"
        << body.type().pretty() << '\'';
    }

    auto &f=function_map[id];
    f.type=signature.type;
    f.parameter_ids=signature.parameter_ids;
    f.body=body;
    local_variable_map.clear();
  }
  else if(c=="set-logic")
  {
    if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after set-logic");

    logic=smt2_tokenizer.get_buffer();
  }
  else if(c=="define-fun")
  {
    if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after define-fun");

    irep_idt id=smt2_tokenizer.get_buffer();

    if(function_map.find(id)!=function_map.end())
      throw error() << "function `" << id << "' declared twice";

    local_variable_map.clear();

    auto signature=function_signature();
    exprt body=expression();

    auto &f=function_map[id];
    f.type=signature.type;
    f.parameter_ids=signature.parameter_ids;
    f.body=body;
    local_variable_map.clear();
  }
  else if(c=="synth-fun" || c=="synth-inv")
  {
    if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after synth-fun");

    irep_idt id=smt2_tokenizer.get_buffer();

    if(function_map.find(id)!=function_map.end())
      throw error() << "function `" << id << "' declared twice";

    auto signature=(id=="inv-f")?
      inv_function_signature() : function_signature();

    NTDef_seq();

    auto &f=function_map[id];
    f.type=signature.type;
    f.parameter_ids=signature.parameter_ids;
    f.body=nil_exprt();

    synth_fun_set.insert(id);
  }
  else if(c=="declare-var")
  {
    if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after declare-var");

    irep_idt id=smt2_tokenizer.get_buffer();

    if(variable_map.find(id)!=variable_map.end())
      throw error() << "variable `" << id << "' declared twice";

    variable_map[id]=sort();
  }
  else if(c=="declare-primed-var")
  {
    if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after declare-primed-var");

    irep_idt id=smt2_tokenizer.get_buffer();
    irep_idt id_prime=smt2_tokenizer.get_buffer()+"!";

    if(variable_map.find(id)!=variable_map.end())
      throw error("variable declared twice");

    variable_map[id]=sort();

    if(variable_map.find(id_prime)!=variable_map.end())
      throw error("variable declared twice");

    variable_map[id_prime]=variable_map[id];
  }
  else if(c=="constraint")
  {
    constraints.push_back(expression());
  }
  else if(c=="inv-constraint")
  {
    ignore_command();
    generate_invariant_constraints();
  }
  else if(c=="set-options")
  {
    ignore_command();
  }
  else if(c=="check-synth")
  {
    action=c;
  }
  else
    ignore_command();
}

sygus_parsert::signature_with_parameter_idst sygus_parsert::inv_function_signature()
{
  if(smt2_tokenizer.next_token()!=smt2_tokenizert::OPEN)
    throw error("expected '(' at beginning of signature");

  mathematical_function_typet::domaint domain;
  std::vector<irep_idt> parameter_ids;

  while(smt2_tokenizer.peek()!=smt2_tokenizert::CLOSE)
  {
    if(smt2_tokenizer.next_token()!=smt2_tokenizert::OPEN)
      throw error("expected '(' at beginning of parameter");

    if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
      throw error("expected symbol in parameter");

    const irep_idt id=smt2_tokenizer.get_buffer();
    const auto parameter_type = sort();
    domain.push_back(parameter_type);
    parameter_ids.push_back(id);
    local_variable_map[id]=parameter_type;

    if(smt2_tokenizer.next_token()!=smt2_tokenizert::CLOSE)
      throw error("expected ')' at end of parameter");
  }

  smt2_tokenizer.next_token(); // eat the ')'

  auto type = mathematical_function_typet(domain, bool_typet());
  return signature_with_parameter_idst(type, parameter_ids);
}

function_application_exprt sygus_parsert::apply_function_to_variables(
  invariant_constraint_functiont function_type,
  invariant_variablet var_use)
{
  std::string suffix;
  if(var_use == PRIMED)
    suffix = "!";

  std::string id;
  switch(function_type)
  {
  case PRE:
    id = "pre-f";
    break;
  case INV:
    id = "inv-f";
    break;
  case TRANS:
    id = "trans-f";
    break;
  case POST:
    id = "post-f";
    break;
  }

  if(function_map.find(id) == function_map.end())
    throw error() << "undeclared function `" << id << '\'';

  const auto &f = function_map[id];

  exprt::operandst arguments;
  arguments.resize(f.type.domain().size());

  assert(f.parameter_ids.size()==f.type.domain().size());

  // get arguments
  for(std::size_t i = 0; i < f.type.domain().size(); i++)
  {
    std::string var_id = id2string(f.parameter_ids[i]) + suffix;
    const typet &var_type = f.type.domain()[i];
    // Allow implicit variable declaration in `inv-constraint`
    variable_map.emplace(var_id, var_type);

    arguments[i] = symbol_exprt(var_id, var_type);
  }

  return function_application_exprt(
    symbol_exprt(id, f.type),
    arguments,
    f.type.codomain());
}

void sygus_parsert::generate_invariant_constraints()
{
  // pre-condition application
  function_application_exprt pre_f =
    apply_function_to_variables(PRE, UNPRIMED);

  // invariant application
  function_application_exprt inv =
    apply_function_to_variables(INV, UNPRIMED);

  function_application_exprt primed_inv =
    apply_function_to_variables(INV, PRIMED);

  // transition function application
  function_application_exprt trans_f =
    apply_function_to_variables(TRANS, UNPRIMED);

  //post-condition function application
  function_application_exprt post_f =
    apply_function_to_variables(POST, UNPRIMED);

  // create constraints
  implies_exprt pre_condition(pre_f, inv);
  constraints.push_back(pre_condition);

  and_exprt inv_and_transition(inv, trans_f);
  implies_exprt transition_condition(inv_and_transition, primed_inv);
  constraints.push_back(transition_condition);

  implies_exprt post_condition(inv, post_f);
  constraints.push_back(post_condition);
}

void sygus_parsert::NTDef_seq()
{
  uint8_t openCount = 0u;
  while(smt2_tokenizer.peek()!=smt2_tokenizert::CLOSE || openCount)
  {
    switch(smt2_tokenizer.next_token())
    {
      case smt2_tokenizert::OPEN:
      ++openCount;
      break;
      case smt2_tokenizert::CLOSE:
      --openCount;
      break;
      case smt2_tokenizert::END_OF_FILE:
      case smt2_tokenizert::KEYWORD:
      case smt2_tokenizert::NONE:
      case smt2_tokenizert::NUMERAL:
      case smt2_tokenizert::STRING_LITERAL:
      case smt2_tokenizert::SYMBOL:
      // Ignore grammar.
      break;
    }
  }
}

void sygus_parsert::GTerm_seq()
{
  while(smt2_tokenizer.peek()!=smt2_tokenizert::CLOSE)
  {
    GTerm();
  }
}

void sygus_parsert::NTDef()
{
  // (Symbol Sort GTerm+)
  if(smt2_tokenizer.next_token()!=smt2_tokenizert::OPEN)
    throw error("NTDef must begin with '('");

  if(smt2_tokenizer.peek()==smt2_tokenizert::OPEN)
    smt2_tokenizer.next_token(); // symbol might be in another set of parenthesis

  if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
    throw error("NTDef must have a symbol");

  sort();

  GTerm_seq();

  if(smt2_tokenizer.next_token()!=smt2_tokenizert::CLOSE)
    throw error("NTDef must end with ')'");
}

void sygus_parsert::GTerm()
{
  // production rule

  switch(smt2_tokenizer.next_token())
  {
  case smt2_tokenizert::SYMBOL:
  case smt2_tokenizert::NUMERAL:
  case smt2_tokenizert::STRING_LITERAL:
    break;

  case smt2_tokenizert::OPEN:
    while(smt2_tokenizer.peek()!=smt2_tokenizert::CLOSE)
    {
      GTerm();
    }

    smt2_tokenizer.next_token(); // eat ')'
    break;

  case smt2_tokenizert::NONE:
  case smt2_tokenizert::END_OF_FILE:
  case smt2_tokenizert::KEYWORD:
  case smt2_tokenizert::CLOSE:
    throw error("Unexpected GTerm");
  }
}

void sygus_parsert::expand_function_applications(exprt &expr)
{
  for(exprt &op : expr.operands())
    expand_function_applications(op);

  if(expr.id()==ID_function_application)
  {
    auto &app=to_function_application_expr(expr);

    // look it up
    DATA_INVARIANT(app.function().id()==ID_symbol, "function must be symbol");
    irep_idt identifier=to_symbol_expr(app.function()).get_identifier();
    auto f_it=function_map.find(identifier);

    if(f_it!=function_map.end())
    {
      const auto &f=f_it->second;

      if(synth_fun_set.find(identifier)!=synth_fun_set.end())
      {
        to_symbol_expr(app.function()).set_identifier("synth_fun::"+id2string(identifier));
        return; // do not expand
      }

      assert(f.type.domain().size()==
             app.arguments().size());

      replace_symbolt replace_symbol;

      std::map<irep_idt, exprt> parameter_map;
      for(std::size_t i=0; i<f.type.domain().size(); i++)
      {
        const auto &parameter_type = f.type.domain()[i];
        const auto &parameter_id = f.parameter_ids[i];

        replace_symbol.insert(
          symbol_exprt(parameter_id, parameter_type),
          app.arguments()[i]);
      }

      exprt body=f.body;
      replace_symbol(body);
      expand_function_applications(body);
      expr=body;
    }
  }
}

typet sygus_parsert::sort()
{
  switch(smt2_tokenizer.next_token())
  {
  case smt2_tokenizert::SYMBOL:
    if(smt2_tokenizer.get_buffer()=="Bool")
      return bool_typet();
    else if(smt2_tokenizer.get_buffer()=="Int")
      return integer_typet();
    else if(smt2_tokenizer.get_buffer()=="Real")
      return real_typet();
    else
      throw error() << "unexpected sort: `" << smt2_tokenizer.get_buffer() << '\'';

  case smt2_tokenizert::OPEN:
    if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
      throw error("expected symbol after '(' in a sort");

    if(smt2_tokenizer.get_buffer()=="_")
    {
      // SyGuS-IF v2.0 now matches smt-lib syntax
      if(smt2_tokenizer.next_token() != smt2_tokenizert::SYMBOL)
        throw error("expected symbol after '_' in a sort");

      if(smt2_tokenizer.get_buffer() == "BitVec")
      {
        if(smt2_tokenizer.next_token() != smt2_tokenizert::NUMERAL)
          throw error("expected numeral as bit-width");

        auto width = std::stoll(smt2_tokenizer.get_buffer());

        // eat the ')'
        if(smt2_tokenizer.next_token() != smt2_tokenizert::CLOSE)
          throw error("expected ')' at end of sort");

        return unsignedbv_typet(width);
      }
    }
    else if(smt2_tokenizer.get_buffer()=="BitVec")
    {
      // this has slightly different symtax compared to SMT-LIB2
      if(smt2_tokenizer.next_token()!=smt2_tokenizert::NUMERAL)
        throw error("expected number after BitVec");

      auto width=std::stoll(smt2_tokenizer.get_buffer());

      if(smt2_tokenizer.next_token()!=smt2_tokenizert::CLOSE)
        throw error("expected ')' after BitVec width");

      return unsignedbv_typet(width);
    }
    else
      throw error() << "unexpected sort: `" << smt2_tokenizer.get_buffer() << '\'';

  case smt2_tokenizert::NONE:
  case smt2_tokenizert::END_OF_FILE:
  case smt2_tokenizert::STRING_LITERAL:
  case smt2_tokenizert::NUMERAL:
  case smt2_tokenizert::KEYWORD:
  case smt2_tokenizert::CLOSE:
  default:
    throw error() << "unexpected token in a sort " << smt2_tokenizer.get_buffer();
  }
}

