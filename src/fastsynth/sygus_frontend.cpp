#include "sygus_frontend.h"

#include "smt2_parser.h"

#include <util/expr.h>
#include <util/std_types.h>
#include <util/std_expr.h>

#include <cassert>
#include <fstream>
#include <iostream>

class sygus_parsert:public new_smt2_parsert
{
public:
  explicit sygus_parsert(std::istream &_in):
    new_smt2_parsert(_in)
  {
  }

  virtual void command() override;

  std::string action;

  std::list<exprt> constraints;

  // parse errors
  virtual void error(const std::string &s) override
  {
    std::cerr << "Parsing error: " << s << '\n';
    ok=false;
  }

  exprt expression();
  exprt::operandst operands();
};

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

void sygus_parsert::command()
{
  if(buffer=="set-logic")
  {
    if(next_token()!=SYMBOL)
    {
      error("expected logic");
      return;
    }

    std::cout << "Logic: " << buffer << "\n";
  }
  else if(buffer=="define-fun")
  {
    new_smt2_parsert::command();
  }
  else if(buffer=="declare-var")
  {
    new_smt2_parsert::command();
  }
  else if(buffer=="constraint")
  {
    constraints.push_back(expression());
  }
  else if(buffer=="check-synth")
    action=buffer;
  else
    new_smt2_parsert::command();
}

int sygus_frontend(const cmdlinet &cmdline)
{
  assert(cmdline.args.size()==1);

  std::ifstream in(cmdline.args.front());

  if(!in)
  {
    std::cerr << "Failed to open input file\n";
    return 10;
  }

  sygus_parsert parser(in);

  parser();

  if(!parser)
    return 20;

  return 0;
}
