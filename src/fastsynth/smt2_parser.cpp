/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2_parser.h"

#include <util/arith_tools.h>

#include "function.h"

void new_smt2_parsert::command_sequence()
{
  while(next_token()==OPEN)
  {
    if(next_token()!=SYMBOL)
    {
      ok=false;
      error() << "expected symbol as command" << eom;
      return;
    }

    command(buffer);

    switch(next_token())
    {
    case END_OF_FILE:
      ok=false;
      error() << "expected closing parenthesis at end of command, but got EOF" << eom;
      return;

    case CLOSE:
      // what we expect
      break;

    default:
      ok=false;
      error() << "expected end of command" << eom;
      return;
    }
  }

  if(token!=END_OF_FILE)
  {
    ok=false;
    error() << "unexpected token in command sequence" << eom;
  }
}

void new_smt2_parsert::ignore_command()
{
  std::size_t parentheses=0;
  while(true)
  {
    switch(peek())
    {
    case OPEN:
      next_token();
      parentheses++;
      break;

    case CLOSE:
      if(parentheses==0)
        return; // done

      next_token();
      parentheses--;
      break;

    case END_OF_FILE:
      ok=false;
      error() << "unexpected EOF in command" << eom;
      return;

    default:
      next_token();
    }
  }
}
exprt::operandst new_smt2_parsert::operands()
{
  exprt::operandst result;

  while(peek()!=CLOSE)
    result.push_back(expression());

  next_token(); // eat the ')'

  return result;
}


let_exprt new_smt2_parsert::let_expression(bool first_in_chain)
{
  let_exprt result;

  if(peek()!=OPEN && !first_in_chain)
  {
    // no need for chaining, single let exprt.
    result.operands()=operands();
    return result;
  }
  else
  {
    if(peek()==OPEN && first_in_chain)
    {
      next_token(); // eat the '('that starts the bindings list
    }

    next_token(); // eat the '(' that starts the next binding

    // get op0
    if(next_token()==SYMBOL)
    {
      symbol_exprt operand0(buffer, sort());
      result.op0() = operand0;
    }
    else
    {
      ok=false;
      error() << "expected symbol in let expression" << eom;
      return result;
    }

    // get op1
    result.op1() = expression();
    next_token(); // eat the ')' that closes this binding

    if(peek()!=CLOSE) // we are still in a chain of bindings
    {
      // get op2
      result.op2() = let_expression(false);
      result.type() = result.op2().type();
    }
    else
    {
      // we are at the end of the chain
      next_token(); // eat the ')' that closes the bindings list

      if(peek()!=OPEN)
      {
        ok=false;
        error() << "let expects where here" << eom;
        return result;
      }

      result.op2() = expression();
      result.type()=result.op2().type();
      next_token(); // eat the final ')' that closes the let exprt
    }
  }
  return result;
}

exprt new_smt2_parsert::function_application(
  const irep_idt &identifier,
  const exprt::operandst &op)
{
  const auto &f = function_map[identifier];

  function_application_exprt result;

  result.function()=symbol_exprt(identifier, f.type);
  result.arguments()=op;

  // check the arguments
  if(op.size()!=f.type.variables().size())
  {
    ok=false;
    error() << "wrong number of arguments for function" << eom;
    return nil_exprt();
  }

  for(std::size_t i=0; i<op.size(); i++)
  {
    if(op[i].type() != f.type.variables()[i].type())
    {
      ok=false;
      error() << "wrong type for arguments for function" << eom;
      return result;
    }
  }

  result.type()=f.type.range();
  return result;
}


void new_smt2_parsert::fix_ite_operation_result_type(if_exprt &expr)
{
  if(expr.op0().id()!=ID_bool)
    expr.op0().type()=bool_typet();

  if(expr.op1().type()!=expr.op2().type())
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
    if(expr.op1().type()!=expr.op2().type())
    {
      ok=false;
      error() << "mismatching types for ite operand" << eom;
    }
  }

  expr.type()=expr.op1().type();
}

void new_smt2_parsert::fix_binary_operation_operand_types(exprt &expr)
{
  // TODO: deal with different widths of bitvector
  if(expr.operands().size()!=2)
  {
    error() << "two operands expected for binary operation " << expr.id() << eom;
    return;
  }

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
    {
      ok=false;
      error() << "mismatching types for binary operand" << expr.id() << eom;
    }
  }
}


exprt new_smt2_parsert::cast_bv_to_signed(exprt &expr)
{
  if(expr.type().id()==ID_signedbv) // no need to cast
    return expr;

  if(expr.type().id()!=ID_unsignedbv)
  {
    error() << "expected unsigned bitvector" << eom;
    return expr;
  }

 signedbv_typet signed_type(to_unsignedbv_type(expr.type()).get_width());
 typecast_exprt result(expr, signed_type);
 result.op0()=expr;
 result.type()=signed_type;

 return result;
}

exprt new_smt2_parsert::cast_bv_to_unsigned(exprt &expr)
{
  if(expr.type().id()==ID_unsignedbv) // no need to cast
    return expr;

  if(expr.type().id()!=ID_signedbv)
  {
    error() << "expected signed bitvector" << eom;
    return expr;
  }

  unsignedbv_typet unsigned_type(to_signedbv_type(expr.type()).get_width());
  typecast_exprt result(expr, unsigned_type);
  result.op0()=expr;
  result.type()=unsigned_type;
  return result;
}

exprt new_smt2_parsert::expression()
{
  switch(next_token())
  {
  case SYMBOL:
    {
      // hash it
      const irep_idt identifier=buffer;

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
      else if(function_map.find(identifier)!=
              function_map.end())
      {
        return function_application(identifier, exprt::operandst());
      }
      else
      {
        ok=false;
        error() << "unknown symbol " << buffer << eom;
        return symbol_exprt(identifier, bool_typet());
      }
    }

  case NUMERAL:
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

  case OPEN:
    if(next_token()==SYMBOL)
    {
      // hash it
      const irep_idt id=buffer;

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
        return result;
      }
      else if(id==ID_or)
      {
        or_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id==ID_xor)
      {
        notequal_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id==ID_not)
      {
        not_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id=="=")
      {
        equal_exprt result;
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=bool_typet();
        return result;
      }
      else if(id=="<=" || id=="bvule" || id=="bvsle")
      {
        predicate_exprt result(ID_le);
        result.operands()=op;

        fix_binary_operation_operand_types(result);
        result.type()=bool_typet();

        if(id=="bvsle")
        {
          result.op0()=cast_bv_to_signed(result.op0());
          result.op1()=cast_bv_to_signed(result.op1());
        }
        return result;
      }
      else if(id==">=" || id=="bvuge" || id=="bvsge")
      {
        predicate_exprt result(ID_ge);
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=bool_typet();

        if(id=="bvsge")
        {
          result.op0()=cast_bv_to_signed(result.op0());
          result.op1()=cast_bv_to_signed(result.op1());
        }

        return result;
      }
      else if(id=="<" || id=="bvult" || id=="bvslt")
      {
        predicate_exprt result(ID_lt);
        result.operands()=op;

        fix_binary_operation_operand_types(result);
        result.type()=bool_typet();

        if(id=="bvslt")
        {
          result.op0()=cast_bv_to_signed(result.op0());
          result.op1()=cast_bv_to_signed(result.op1());
        }
        return result;
      }
      else if(id==">" || id=="bvugt" || id=="bvsgt")
      {
        predicate_exprt result(ID_gt);
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=bool_typet();

        if(id=="bvsgt")
        {
          result.op0()=cast_bv_to_signed(result.op0());
          result.op1()=cast_bv_to_signed(result.op1());
        }
        return result;
      }
      else if(id=="bvashr")
      {
        if(op.size()!=2)
        {
          ok=false;
          error() << "bit shift must have 2 operands" << eom;
          return nil_exprt();
        }

        ashr_exprt result(op[0], op[1]);
        bv_typet type(0u);
        type.remove(ID_width);
        result.type()=type;
        return result;
      }
      else if(id=="bvlshr" || id=="bvshr")
      {
        if(op.size()!=2)
        {
          ok=false;
          error() << "bit shift must have two operands" << eom;
          return nil_exprt();
        }

        lshr_exprt result(op[0], op[1]);
        bv_typet type(0u);
        type.remove(ID_width);
        result.type()=type;

        return result;
      }
      else if(id=="bvlshr" || id=="bvashl" || id=="bvshl")
      {
        if(op.size()!=2)
        {
          ok=false;
          error() << "bit shift must have two operands" << eom;
          return nil_exprt();
        }

        shl_exprt result(op[0], op[1]);
        bv_typet type(0u);
        type.remove(ID_width);
        result.type()=type;

        return result;
      }
      else if(id=="bvand")
      {
        bitand_exprt result;
        result.operands()=op;

        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();

        return result;
      }
      else if(id=="bvor")
      {
        bitor_exprt result;
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();
        return result;
      }
      else if(id=="bvxor")
      {
        bitxor_exprt result;
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();
        return result;
      }
      else if(id=="bvnot" || id=="bvneg")
      {
        bitnot_exprt result;
        result.operands()=op;
        result.type()=result.op0().type();
        return result;
      }
      else if(id=="bvadd" || id=="+")
      {
        plus_exprt result;
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();
        return result;
      }
      else if(id=="bvsub" || id=="-")
      {
        minus_exprt result;
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();
        return result;
      }
      else if(id=="bvmul" || id=="*")
      {
        mult_exprt result;
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();
        return result;
      }
      else if(id=="bvsdiv" || id=="bvudiv")
      {
        div_exprt result;
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();

        if(id=="bvsdiv")
        {
          result.op0()=cast_bv_to_signed(result.op0());
          result.op1()=cast_bv_to_signed(result.op1());
          return cast_bv_to_unsigned(result);
        }

        return result;
      }
      else if(id=="/" || id=="div")
      {
        div_exprt result;
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();
        return result;
      }
      else if(id=="bvsrem" || id=="bvurem" || id=="%")
      {
        mod_exprt result;
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();

        if(id=="bvsrem")
        {
          result.op0()=cast_bv_to_signed(result.op0());
          result.op1()=cast_bv_to_signed(result.op1());
          return cast_bv_to_unsigned(result);
        }

        return result;
      }
      else if(id=="ite")
      {
        if_exprt result;
        result.operands()=op;
        fix_ite_operation_result_type(result);
        return result;
      }
      else if(id=="=>" || id=="implies")
      {
        implies_exprt result;
        result.operands()=op;
        return result;
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
          return result;
        }
        else if(variable_map.find(id)!=variable_map.end())
        {
          symbol_exprt result(id, variable_map[id]);
          return result;
        }
        else
        {
          error() << "use of undeclared symbol or function " << id << eom;
          return nil_exprt();
        }
      }
    }
    else
    {
      error() << "expected symbol after '(' in an expression" << eom;
      return nil_exprt();
    }

  case END_OF_FILE:
    error() << "EOF in an expression" << eom;
    return nil_exprt();

  default:
    error() << "unexpected token in an expression" << eom;
    return nil_exprt();
  }
}

typet new_smt2_parsert::sort()
{
  switch(next_token())
  {
  case SYMBOL:
    if(buffer=="Bool")
      return bool_typet();
    else if(buffer=="Int")
      return integer_typet();
    else if(buffer=="Real")
      return real_typet();
    else
    {
      error() << "unexpected sort: `" << buffer << '\'' << eom;
      return nil_typet();
    }

  case OPEN:
    if(next_token()!=SYMBOL)
    {
      error() << "expected symbol after '(' in a sort" << eom;
      return nil_typet();
    }

    {
      error() << "unexpected sort: `" << buffer << '\'' << eom;
      return nil_typet();
    }

  default:
    error() << "unexpected token in a sort " << buffer << eom;
    return nil_typet();
  }
}

function_typet new_smt2_parsert::function_signature()
{
  function_typet result;

  if(next_token()!=OPEN)
  {
    error() << "expected '(' at beginning of signature" << eom;
    return result;
  }

  while(peek()!=CLOSE)
  {
    if(next_token()!=OPEN)
    {
      error() << "expected '(' at beginning of parameter" << eom;
      return result;
    }

    if(next_token()!=SYMBOL)
    {
      error() << "expected symbol in parameter" << eom;
      return result;
    }

    auto &var=result.add_variable();
    std::string id=buffer;
    var.set_identifier(id);
    var.type()=sort();
    local_variable_map[id]=var.type();

    if(next_token()!=CLOSE)
    {
      error() << "expected ')' at end of parameter" << eom;
      return result;
    }
  }

  next_token(); // eat the ')'

  result.range()=sort();

  return result;
}

void new_smt2_parsert::command(const std::string &c)
{
  if(c=="declare-var")
  {
    if(next_token()!=SYMBOL)
    {
      error() << "expected a symbol after declare-var" << eom;
      ignore_command();
      return;
    }

    irep_idt id=buffer;

    if(variable_map.find(id)!=variable_map.end())
    {
      error() << "variable declared twice" << eom;
      ignore_command();
      return;
    }

    variable_map[id]=sort();
  }
  else if(c=="define-fun")
  {
    if(next_token()!=SYMBOL)
    {
      error() << "expected a symbol after define-fun" << eom;
      ignore_command();
      return;
    }

    const irep_idt id=buffer;

    if(function_map.find(id)!=function_map.end())
    {
      error() << "function declared twice" << eom;
      ignore_command();
      return;
    }

    local_variable_map.clear();

    auto signature=function_signature();
    exprt body=expression();

    auto &f=function_map[id];
    f.type=signature;
    f.body=body;
    local_variable_map.clear();
  }
  else
    ignore_command();
}
