#include "sygus_parser.h"

#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/replace_symbol.h>

#include <cassert>
#include <fstream>

#include "function.h"

void sygus_parsert::command(const std::string &c)
{
  if(c=="set-logic")
  {
    if(next_token()!=SYMBOL)
    {
      ok=false;
      error() << "expected a symbol after set-logic" << eom;
      ignore_command();
      return;
    }

    logic=buffer;
    status() << "Logic: " << logic << eom;
  }
  else if(c=="define-fun")
  {
    if(next_token()!=SYMBOL)
    {
      ok=false;
      error() << "expected a symbol after define-fun" << eom;
      ignore_command();
      return;
    }

    irep_idt id=buffer;

    if(function_map.find(id)!=function_map.end())
    {
      ok=false;
      error() << "function `" << id << "' declared twice" << eom;
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
  else if(c=="synth-fun" || c=="synth-inv")
  {
    if(next_token()!=SYMBOL)
    {
      error() << "expected a symbol after synth-fun" << eom;
      ignore_command();
      return;
    }

    irep_idt id=buffer;

    if(function_map.find(id)!=function_map.end())
    {
      error() << "function `" << id << " declared twice" << eom;
      ignore_command();
      return;
    }

    auto signature=(id=="inv-f")?
        inv_function_signature() : function_signature();

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
      ok=false;
      error() << "expected a symbol after declare-var" << eom;
      ignore_command();
      return;
    }

    irep_idt id=buffer;

    if(variable_map.find(id)!=variable_map.end())
    {
      ok=false;
      error() << "variable `" << id << "' declared twice" << eom;
      ignore_command();
      return;
    }

    variable_map[id]=sort();
  }
  else if(c=="declare-primed-var")
  {
    if(next_token()!=SYMBOL)
    {
      error() << "expected a symbol after declare-primed-var" << eom;
      ignore_command();
      return;
    }

    irep_idt id=buffer;
    irep_idt id_prime=buffer+"!";

    if(variable_map.find(id)!=variable_map.end())
    {
      error() << "variable declared twice" << eom;
      ignore_command();
      return;
    }

    variable_map[id]=sort();

    if(variable_map.find(id_prime)!=variable_map.end())
    {
      error() << "variable declared twice" << eom;
      ignore_command();
      return;
    }

    variable_map[id_prime]=variable_map[id];

  }
  else if(c=="constraint")
  {
    constraints.push_back(expression());
  }
  else if(c=="inv-constraint")
  {
    ignore_command();
    generate_invariant_constraints();
  }
  else if(c=="set-options")
  {
    ignore_command();
  }
  else if(c=="check-synth")
  {
    action=c;
    status() << "Action: " << action << eom;
  }
  else
    ignore_command();
}

function_typet sygus_parsert::inv_function_signature()
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

  result.range()=bool_typet();

  return result;
}


void sygus_parsert::apply_function_to_variables(
    function_application_exprt &expr,
    invariant_constraint_functiont function_type,
    invariant_variablet var_use)
{
  std::string suffix;
  if(var_use == PRIMED)
    suffix = "!";

  std::string id;
  switch(function_type)
  {
  case PRE:
    id = "pre-f";
    break;
  case INV:
    id = "inv-f";
    break;
  case TRANS:
    id = "trans-f";
    break;
  case POST:
    id = "post-f";
    break;
  }

  expr.function() = symbol_exprt(id, bool_typet());
  if(function_map.find(id) == function_map.end())
  {
    error() << "undeclared function " << id << eom;
    return;
  }
  const auto &f = function_map[id];
  expr.type() = f.type.range();
  expr.arguments().resize(f.type.variables().size());
  // get arguments
  for(std::size_t i = 0; i < f.type.variables().size(); i++)
  {
    std::string var_id = id2string(f.type.variables()[i].get_identifier())
        + suffix;

    if(variable_map.find(var_id) == variable_map.end())
      error() << "use of undeclared variable " << var_id << eom;
    symbol_exprt operand(var_id, f.type.variables()[i].type());
    expr.arguments()[i] = operand;
  }
}


void sygus_parsert::generate_invariant_constraints()
{
  // pre-condition application
  function_application_exprt pre_f;
  apply_function_to_variables(pre_f, PRE, UNPRIMED);

  // invariant application
  function_application_exprt inv;
  function_application_exprt primed_inv;
  apply_function_to_variables(inv, INV, UNPRIMED);
  apply_function_to_variables(primed_inv, INV, PRIMED);

  // transition function application
  function_application_exprt trans_f;
  apply_function_to_variables(trans_f, TRANS, UNPRIMED);

  //post-condition function application
  function_application_exprt post_f;
  apply_function_to_variables(post_f, POST, UNPRIMED);

  // create constraints
  implies_exprt pre_condition(pre_f, inv);
  constraints.push_back(pre_condition);

  and_exprt inv_and_transition(inv, trans_f);
  implies_exprt transition_condition(inv_and_transition, primed_inv);
  constraints.push_back(transition_condition);

  implies_exprt post_condition(inv, post_f);
  constraints.push_back(post_condition);
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
    ok=false;
    error() << "NTDef must begin with '('" << eom;
    return;
  }

  if(peek()==OPEN)
    next_token(); // symbol might be in another set of parenthesis

  if(next_token()!=SYMBOL)
  {
    ok=false;
    error() << "NTDef must have a symbol" << eom;
    return;
  }

  sort();

  GTerm_seq();

  if(next_token()!=CLOSE)
  {
    ok=false;
    error() << "NTDef must end with ')'" << eom;
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
    error() << "Unexpected GTerm" << eom;
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
      {
        app.function().set_identifier("synth_fun::"+id2string(identifier));
        return; // do not expand
      }

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
      expand_function_applications(body);
      expr=body;
    }
  }
}
