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
      else if(id=="<=")
      {
        predicate_exprt result(ID_le);
        result.operands()=op;
        return result;
      }
      else if(id==">=")
      {
        predicate_exprt result(ID_ge);
        result.operands()=op;
        return result;
      }
      else if(id=="<")
      {
        predicate_exprt result(ID_lt);
        result.operands()=op;
        return result;
      }
      else if(id==">")
      {
        predicate_exprt result(ID_gt);
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
    ignore_command();
  }
  else if(c=="declare-var")
  {
    if(next_token()!=SYMBOL)
    {
      error("expected a symbol after declare-var");
      ignore_command();
      return;
    }

    if(variable_map.find(buffer)!=variable_map.end())
    {
      error("variable declared twice");
      ignore_command();
      return;
    }

    variable_map[buffer]=sort();
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

