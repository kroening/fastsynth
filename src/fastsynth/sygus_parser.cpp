#include "sygus_parser.h"

#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/replace_symbol.h>

#include <cassert>
#include <fstream>
#include <iostream>

#include "function.h"

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

    local_variable_map.clear();

    auto signature=function_signature();
    exprt body=expression();

    auto &f=function_map[id];
    f.type=signature;
    f.body=body;
    local_variable_map.clear();
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

    synth_fun_set.insert(id);
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
  // it is not necessary to give a syntactic template
  if(peek()!=OPEN)
    return;

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

  if(peek()==OPEN)
    next_token(); // symbol might be in another set of parenthesis

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
  case NUMERAL:
  case STRING_LITERAL:
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

void sygus_parsert::expand_function_applications(exprt &expr)
{
  for(exprt &op : expr.operands())
    expand_function_applications(op);

  if(expr.id()==ID_function_application)
  {
    auto &app=to_function_application_expr(expr);

    // look it up
    irep_idt identifier=app.function().get_identifier();
    auto f_it=function_map.find(identifier);

    if(f_it!=function_map.end())
    {
      const auto &f=f_it->second;

      if(synth_fun_set.find(identifier)!=synth_fun_set.end())
        return; // do not expand

      assert(f.type.variables().size()==
             app.arguments().size());

      replace_symbolt replace_symbol;

      std::map<irep_idt, exprt> parameter_map;
      for(std::size_t i=0; i<f.type.variables().size(); i++)
      {
        const irep_idt p_identifier=
          f.type.variables()[i].get_identifier();

        replace_symbol.insert(p_identifier, app.arguments()[i]);
      }

      exprt body=f.body;
      replace_symbol(body);

      expr=body;
    }
  }
}
