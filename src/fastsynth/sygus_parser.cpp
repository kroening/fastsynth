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
    return symbol_exprt(buffer, bool_typet());

  case OPEN:
    if(next_token()==SYMBOL)
    {
      const auto op=operands();
      if(buffer=="and")
      {
        and_exprt result;
        result.operands()=op;
        return result;
      }
      else if(buffer=="or")
      {
        or_exprt result;
        result.operands()=op;
        return result;
      }
      else if(buffer=="not")
      {
        not_exprt result;
        result.operands()=op;
        return result;
      }
      else if(buffer=="=")
      {
        equal_exprt result;
        result.operands()=op;
        return result;
      }
      else if(buffer=="<=")
      {
        predicate_exprt result(ID_le);
        result.operands()=op;
        return result;
      }
      else if(buffer==">=")
      {
        predicate_exprt result(ID_ge);
        result.operands()=op;
        return result;
      }
      else if(buffer=="<")
      {
        predicate_exprt result(ID_lt);
        result.operands()=op;
        return result;
      }
      else if(buffer==">")
      {
        predicate_exprt result(ID_gt);
        result.operands()=op;
        return result;
      }
      else
      {
        // a defined function?
        function_application_exprt result;
        result.function()=symbol_exprt(buffer);
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

