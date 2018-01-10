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

