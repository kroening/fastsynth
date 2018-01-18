/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2_parser.h"

#include <util/arith_tools.h>

#include <istream>

#include "function.h"

bool smt2_tokenizert::is_simple_symbol_character(char ch)
{
  // any non-empty sequence of letters, digits and the characters
  // ~ ! @ $ % ^ & * _ - + = < > . ? /
  // that does not start with a digit and is not a reserved word.

  return isalnum(ch) ||
     ch=='~' || ch=='!' || ch=='@' || ch=='$' || ch=='%' ||
     ch=='^' || ch=='&' || ch=='*' || ch=='_' || ch=='-' ||
     ch=='+' || ch=='=' || ch=='<' || ch=='>' || ch=='.' ||
     ch=='?' || ch=='/';
}

smt2_tokenizert::tokent smt2_tokenizert::get_simple_symbol()
{
  // any non-empty sequence of letters, digits and the characters
  // ~ ! @ $ % ^ & * _ - + = < > . ? /
  // that does not start with a digit and is not a reserved word.

  buffer.clear();

  char ch;
  while(in.get(ch))
  {
    if(is_simple_symbol_character(ch))
    {
      buffer+=ch;
    }
    else
    {
      in.unget(); // put back
      return SYMBOL;
    }
  }

  // eof -- this is ok here
  if(buffer.empty())
    return END_OF_FILE;
  else
    return SYMBOL;
}

smt2_tokenizert::tokent smt2_tokenizert::get_decimal_numeral()
{
  // we accept any sequence of digits and dots

  buffer.clear();

  char ch;
  while(in.get(ch))
  {
    if(isdigit(ch) || ch=='.')
    {
      buffer+=ch;
    }
    else
    {
      in.unget(); // put back
      return NUMERAL;
    }
  }

  // eof -- this is ok here
  if(buffer.empty())
    return END_OF_FILE;
  else
    return NUMERAL;
}

smt2_tokenizert::tokent smt2_tokenizert::get_bin_numeral()
{
  // we accept any sequence of '0' or '1'

  buffer.clear();
  buffer+='#';
  buffer+='b';

  char ch;
  while(in.get(ch))
  {
    if(ch=='0' || ch=='1')
    {
      buffer+=ch;
    }
    else
    {
      in.unget(); // put back
      return NUMERAL;
    }
  }

  // eof -- this is ok here
  if(buffer.empty())
    return END_OF_FILE;
  else
    return NUMERAL;
}

smt2_tokenizert::tokent smt2_tokenizert::get_hex_numeral()
{
  // we accept any sequence of '0'-'9', 'a'-'f', 'A'-'F'

  buffer.clear();
  buffer+='#';
  buffer+='x';

  char ch;
  while(in.get(ch))
  {
    if(isxdigit(ch))
    {
      buffer+=ch;
    }
    else
    {
      in.unget(); // put back
      return NUMERAL;
    }
  }

  // eof -- this is ok here
  if(buffer.empty())
    return END_OF_FILE;
  else
    return NUMERAL;
}

smt2_tokenizert::tokent smt2_tokenizert::get_quoted_symbol()
{
  // any sequence of printable ASCII characters (including space,
  // tab, and line-breaking characters) except for the backslash
  // character \, that starts and ends with | and does not otherwise
  // contain |

  buffer.clear();

  char ch;
  while(in.get(ch))
  {
    if(ch=='|')
      return SYMBOL; // done
    buffer+=ch;
  }

  // Hmpf. Eof before end of quoted symbol. This is an error.
  error("EOF within quoted symbol");
  return ERROR;
}

smt2_tokenizert::tokent smt2_tokenizert::get_string_literal()
{
  buffer.clear();

  char ch;
  while(in.get(ch))
  {
    if(ch=='"')
    {
      // quotes may be escaped by repeating
      if(in.get(ch))
      {
        if(ch=='"')
        {
        }
        else
        {
          in.unget();
          return STRING_LITERAL; // done
        }
      }
      else
        return STRING_LITERAL; // done
    }
    buffer+=ch;
  }

  // Hmpf. Eof before end of string literal. This is an error.
  ok=false;
  error("EOF within string literal");
  return ERROR;
}

smt2_tokenizert::tokent smt2_tokenizert::next_token()
{
  if(peeked)
    return peeked=false, token;

  char ch;

  while(in.get(ch))
  {
    switch(ch)
    {
    case ' ':
    case '\n':
    case '\r':
    case '\t':
    case static_cast<char>(160): // non-breaking space
      // skip any whitespace
      break;

    case ';': // comment
      // skip until newline
      while(in.get(ch) && ch!='\n')
      {
        // ignore
      }
      break;

    case '(':
      // produce sub-expression
      return token=OPEN;

    case ')':
      // done with sub-expression
      return token=CLOSE;

    case '|': // quoted symbol
      return token=get_quoted_symbol();

    case '"': // string literal
      return token=get_string_literal();

    case ':': // keyword
      return token=get_simple_symbol();

    case '#':
      if(in.get(ch))
      {
        if(ch=='b')
          return token=get_bin_numeral();
        else if(ch=='x')
          return token=get_hex_numeral();
        else
        {
          ok=false;
          error("unknown numeral token");
          return token=ERROR;
        }
      }
      else
      {
        ok=false;
        error("unexpected EOF in numeral token");
        return token=ERROR;
      }
      break;

    default: // likely a simple symbol or a numeral
      if(isdigit(ch))
      {
        in.unget();
        return token=get_decimal_numeral();
      }
      else if(is_simple_symbol_character(ch))
      {
        in.unget();
        return token=get_simple_symbol();
      }
      else
      {
        // illegal character, error
        ok=false;
        error("unexpected character");
        return token=ERROR;
      }
    }
  }

  return token=END_OF_FILE;
}

void new_smt2_parsert::command_sequence()
{
  while(next_token()==OPEN)
  {
    if(next_token()!=SYMBOL)
    {
      ok=false;
      error("expected symbol as command");
      return;
    }

    command(buffer);

    switch(next_token())
    {
    case END_OF_FILE:
      ok=false;
      error("expected closing parenthesis at end of command, but got EOF");
      return;

    case CLOSE:
      // what we expect
      break;

    default:
      ok=false;
      error("expected end of command");
      return;
    }
  }

  if(token!=END_OF_FILE)
  {
    ok=false;
    error("unexpected token: "+buffer);
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
      error("unexpected EOF in command");
      return;

    default:
      next_token();
    }
  }
}
#include <iostream>
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
    if(next_token() == SYMBOL)
    {
      symbol_exprt operand0(buffer, sort());
      result.op0() = operand0;
    }
    else
      error("expected symbol");

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
      if(peek()!= OPEN)
        error("let expects where here");
      result.op2() = expression();
      result.type()=result.op2().type();
      next_token(); // eat the final ')' that closes the let exprt
    }
  }
  return result;
}


exprt new_smt2_parsert::expand_function(irep_idt ID, exprt::operandst op)
{
  auto &f = function_map[ID];
//  if(f.body==nil_typet())
  {
    function_application_exprt result;
    result.function()=symbol_exprt(ID);
    result.arguments()=op;
    // check arguments
    if(op.size()!=f.type.variables().size())
    {
      error("wrong number of arguments for function ");
      return nil_exprt();
    }

    for(std::size_t i=0; i<op.size(); i++)
    {
      if(op[i].type()!=f.type.variables()[i].type())
      {
        error("wrong type for arguments for function ");
        std::cout <<ID.c_str();
        std::cout<<"\nwrong type: expected: " << f.type.variables()[i].type().id_string();
        std::cout<<" got: "<<op[i].type().id()<<std::endl;


        return nil_exprt();
      }
    }
    result.type()=f.type.range();
    return result;
  }
}


void new_smt2_parsert::fix_ite_operation_result_type(if_exprt &expr)
{
  if(expr.operands().size()!=3)
    error("ite operation expects 3 operands");
  if(expr.op1().type()!=expr.op2().type() &&
      !(expr.op1().id()==ID_constant || expr.op2().id()==ID_constant))
    error("mismatching types for ite operands");

  if(expr.op0().id()!=ID_bool)
  {
    expr.op0().type()=bool_typet();
  }

  if(expr.op1().id()==ID_constant && expr.op2().id()!=ID_constant)
    expr.op1().type()=expr.op2().type();

  if(expr.op2().id()==ID_constant && expr.op1().id()!=ID_constant)
    expr.op2().type()=expr.op1().type();

  expr.type()=expr.op1().type();

}

void new_smt2_parsert::fix_binary_operation_result_type(exprt &expr)
{
  if(expr.operands().size()!=2)
    error("binary operation expects 2 operands");
  if(expr.op0().type()!=expr.op1().type() &&
      !(expr.op0().id()==ID_constant || expr.op1().id()==ID_constant))
    error("mismatching types for binary operand" + expr.id_string());

  if(expr.op0().id()==ID_constant && expr.op1().id()!=ID_constant)
    expr.op0().type()=expr.op1().type();

  if(expr.op1().id()==ID_constant && expr.op0().id()!=ID_constant)
    expr.op1().type()=expr.op0().type();

  expr.type()=expr.op0().type();
}

exprt new_smt2_parsert::expression()
{
  switch(next_token())
  {
  case SYMBOL:
    if(buffer=="true")
      return true_exprt();
    else if(buffer=="false")
      return false_exprt();
    else if(variable_map.find(buffer)!=variable_map.end())
    {
      return symbol_exprt(buffer, variable_map[buffer]);
    }
    else
      return symbol_exprt(buffer, bool_typet());

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
      std::string id=buffer;

      if(buffer=="let")
      {
        // bool indicates first in chain
        return let_expression(true);
      }

      const auto op=operands();

      if(id=="and")
      {
        and_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id=="or")
      {
        or_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id=="not")
      {
        not_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id=="=")
      {
        equal_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id=="<=" || id=="bvule" || id=="bvsle")
      {
        predicate_exprt result(ID_le);
        result.operands()=op;
        return result;
      }
      else if(id==">=" || id=="bvuge" || id=="bvsge")
      {
        predicate_exprt result(ID_ge);
        result.operands()=op;
        return result;
      }
      else if(id=="<" || id=="bvult" || id=="bvslt")
      {
        predicate_exprt result(ID_lt);
        result.operands()=op;
        result.type()=bool_typet();
        return result;
      }
      else if(id==">" || id=="bvugt" || id=="bvsgt")
      {
        predicate_exprt result(ID_gt);
        result.operands()=op;
        return result;
      }
      else if(id=="bvashr")
      {
        if(op.size()!=2)
          error("bit shift must have 2 operands");

        ashr_exprt result(op[0], op[1]);
        bv_typet type(0u);
        type.remove(ID_width);
        result.type()=type;
        return result;
      }
      else if(id=="bvlshr" || id=="bvshr")
      {
        if(op.size()!=2)
          error("bit shift must have 2 operands");

        lshr_exprt result(op[0], op[1]);
        bv_typet type(0u);
        type.remove(ID_width);
        result.type()=type;
        return result;
      }
      else if(id=="bvlshr" || id=="bvashl" || id=="bvshl")
      {
        if(op.size()!=2)
          error("bit shift must have 2 operands");

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
        bv_typet type(0u);
        type.remove(ID_width);
        result.type()=type;
        return result;
      }
      else if(id=="bvor")
      {
        bitor_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id=="bvxor")
      {
        bitxor_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id=="bvnot" || id=="bvneg")
      {
        bitnot_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id=="bvadd" || id=="+")
      {
        plus_exprt result;
        result.operands()=op;
        fix_binary_operation_result_type(result);
        return result;
      }
      else if(id=="bvsub" || id=="-")
      {
        minus_exprt result;
        result.operands()=op;
        fix_binary_operation_result_type(result);
        return result;
      }
      else if(id=="bvmul" || id=="*")
      {
        mult_exprt result;
        result.operands()=op;
        fix_binary_operation_result_type(result);
        return result;
      }
      else if(id=="bvsdiv" || id=="bvudiv" || id=="/")
      {
        div_exprt result;
        result.operands()=op;
        fix_binary_operation_result_type(result);
        return result;
      }
      else if(id=="bvsrem" || id=="bvurem" || id=="%")
      {
        mod_exprt result;
        result.operands()=op;
        fix_binary_operation_result_type(result);
        return result;
      }
      else if(id=="ite")
      {
        if_exprt result;
        result.operands()=op;
        fix_ite_operation_result_type(result);
        return result;
      }
      else if(buffer=="=>" || buffer=="implies")
      {
        implies_exprt result;
        result.operands()=op;
        return result;
      }
      else
      {
        if(function_map.count(id)!=0)
        {
          return expand_function(id, op);
        }
        else if(variable_map.find(id)!=variable_map.end())
        {
          symbol_exprt result(id, variable_map[id]);
          return result;
        }
        else
        {
          error("use of undeclared symbol or function" + id);
        }
      }
    }
    else
    {
      error("expected symbol after '(' in an expression");
      return nil_exprt();
    }

  case END_OF_FILE:
    error("EOF in an expression");
    return nil_exprt();

  default:
    error("unexpected token in an expression");
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
      error("unexpected sort");
      return nil_typet();
    }

  case OPEN:
    if(next_token()!=SYMBOL)
    {
      error("expected symbol after '(' in a sort");
      return nil_typet();
    }

    if(buffer=="BitVec")
    {
      if(next_token()!=NUMERAL)
      {
        error("expected number after BitVec");
        return nil_typet();
      }

      auto width=std::stoll(buffer);

      if(next_token()!=CLOSE)
      {
        error("expected ')' after BitVec width");
        return nil_typet();
      }

      return bv_typet(width);
    }
    else
    {
      error("unexpected sort");
      return nil_typet();
    }

  default:
    error("unexpected token in a sort");
    return nil_typet();
  }
}

function_typet new_smt2_parsert::function_signature()
{
  function_typet result;

  if(next_token()!=OPEN)
  {
    error("expected '(' at beginning of signature");
    return result;
  }

  while(peek()!=CLOSE)
  {
    if(next_token()!=OPEN)
    {
      error("expected '(' at beginning of parameter");
      return result;
    }

    if(next_token()!=SYMBOL)
    {
      error("expected symbol in parameter");
      return result;
    }

    auto &var=result.add_variable();

    var.set_identifier(buffer);
    var.type()=sort();

    if(next_token()!=CLOSE)
    {
      error("expected ')' at end of parameter");
      return result;
    }
  }

  next_token(); // eat the ')'

  result.range()=sort();

  return result;
}
