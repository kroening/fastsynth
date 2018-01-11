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

