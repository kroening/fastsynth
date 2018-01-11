/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2_parser.h"

#include <util/std_expr.h>

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

exprt::operandst new_smt2_parsert::operands()
{
  exprt::operandst result;

  while(peek()!=CLOSE)
    result.push_back(expression());

  next_token(); // eat the ')'

  return result;
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
    else
      return symbol_exprt(buffer, bool_typet());

  case NUMERAL:
    if(buffer.size()>=2 && buffer[0]=='#' && buffer[0]=='x')
    {
      mp_integer value=
        string2integer(std::string(buffer, 2, std::string::npos), 16);
      bv_typet type;
      std::size_t width = 4*buffer.size() - 2;
      assert(width!=0 && width%4==0);
      type.set_width(width);
      constant_exprt expr(type);
      expr.set_value(integer2binary(value,width));
      return expr;
    }
    else if(buffer.size()>=2 && buffer[0]=='#' && buffer[0]=='b')
    {
      mp_integer value=
        string2integer(std::string(buffer, 2, std::string::npos), 2);
      bv_typet type;
      std::size_t width = buffer.size() - 2;
      assert(width!=0 && width%2==0);
      type.set_width(width);
      constant_exprt expr(type);
      expr.set_value(integer2binary(value,width));
      return expr;
    }
    else
    {
      return constant_exprt();
    }

  case OPEN:
    if(next_token()==SYMBOL)
    {
      std::string id=buffer;
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
        ashr_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id=="bvlshr" || id=="bvshr")
      {
        lshr_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id=="bvlshr" || id=="bvashl" || id=="bvshl")
      {
        shl_exprt result;
        result.operands()=op;
        return result;
      }

      else if(id=="bvand")
      {
        bitand_exprt result;
        result.operands()=op;
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
        return result;

      }
      else if(id=="bvsub" || id=="-")
      {
        minus_exprt result;
        result.operands()=op;
        return result;

      }
      else if(id=="bvmul" || id=="*")
      {
        mult_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id=="bvsdiv" || id=="bvudiv" || id=="/")
      {
        div_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id=="bvsrem" || id=="bvurem" || id=="%")
      {
        mod_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id=="ite")
      {
        if_exprt result;
        result.operands()=op;
        return result;
      }
      else if(buffer=="=>" || buffer=="implies")
      {
        implies_exprt result;
        result.operands()=op;
        return result;
      }
      else if(buffer=="let")
      {
        let_exprt result;
        result.operands()=op;
        return result;
      }
      else
      {
        // a defined function?
        function_application_exprt result;
        result.function()=symbol_exprt(id);
        result.arguments()=op;
        return result;
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
