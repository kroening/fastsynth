#include "sygus_parser.h"

#include <util/std_types.h>
#include <util/std_expr.h>

#include <cassert>
#include <fstream>
#include <iostream>

void sygus_parsert::error(const std::string &s)
{
  std::cerr << "Parsing error: " << s << '\n';
  ok=false;
}

exprt::operandst sygus_parsert::operands()
{
  exprt::operandst result;

  while(peek()!=CLOSE)
    result.push_back(expression());

  next_token(); // eat the ')'

  return result;
}

exprt sygus_parsert::expression()
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
    }
    else if(buffer.size()>=2 && buffer[0]=='#' && buffer[0]=='b')
    {
      mp_integer value=
        string2integer(std::string(buffer, 2, std::string::npos), 2);
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

typet sygus_parsert::sort()
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

void sygus_parsert::command(const std::string &c)
{
  if(c=="set-logic")
  {
    if(next_token()!=SYMBOL)
    {
      error("expected a symbol after set-logic");
      ignore_command();
      return;
    }

    logic=buffer;
    std::cout << "Logic: " << logic << '\n';
  }
  else if(c=="define-fun")
  {
    if(next_token()!=SYMBOL)
    {
      error("expected a symbol after define-fun");
      ignore_command();
      return;
    }

    irep_idt id=buffer;

    if(function_map.find(id)!=function_map.end())
    {
      error("function declared twice");
      ignore_command();
      return;
    }

    auto signature=function_signature();
    exprt body=expression();

    auto &f=function_map[id];
    f.type=signature;
    f.body=body;
  }
  else if(c=="synth-fun")
  {
    if(next_token()!=SYMBOL)
    {
      error("expected a symbol after synth-fun");
      ignore_command();
      return;
    }

    irep_idt id=buffer;

    if(function_map.find(id)!=function_map.end())
    {
      error("function declared twice");
      ignore_command();
      return;
    }

    auto signature=function_signature();
    NTDef_seq();

    auto &f=function_map[id];
    f.type=signature;
    f.body=nil_exprt();
  }
  else if(c=="declare-var")
  {
    if(next_token()!=SYMBOL)
    {
      error("expected a symbol after declare-var");
      ignore_command();
      return;
    }

    irep_idt id=buffer;

    if(variable_map.find(id)!=variable_map.end())
    {
      error("variable declared twice");
      ignore_command();
      return;
    }

    variable_map[id]=sort();
  }
  else if(c=="synth-fun")
  {
    ignore_command();
  }
  else if(c=="constraint")
  {
    constraints.push_back(expression());
  }
  else if(c=="set-options")
  {
    ignore_command();
  }
  else if(c=="check-synth")
  {
    action=c;
    std::cout << "Action: " << action << '\n';
  }
  else
    ignore_command();
}

void sygus_parsert::NTDef_seq()
{
  if(next_token()!=OPEN)
  {
    error("NTDef-sequence must begin with '('");
    return;
  }

  while(peek()!=CLOSE)
  {
    NTDef();
  }

  next_token(); // eat the ')'
}

void sygus_parsert::GTerm_seq()
{
  while(peek()!=CLOSE)
  {
    GTerm();
  }
}

void sygus_parsert::NTDef()
{
  // (Symbol Sort GTerm+)
  if(next_token()!=OPEN)
  {
    error("NTDef must begin with '('");
    return;
  }

  if(next_token()!=SYMBOL)
  {
    error("NTDef must have a symbol");
    return;
  }

  sort();

  GTerm_seq();

  if(next_token()!=CLOSE)
  {
    error("NTDef must end with ')'");
    return;
  }
}

void sygus_parsert::GTerm()
{
  // production rule

  switch(next_token())
  {
  case SYMBOL:
    break;

  case OPEN:
    while(peek()!=CLOSE)
    {
      GTerm();
    }

    next_token(); // eat ')'
    break;

  default:
    error("Unexpected GTerm");
    return;
  }
}

