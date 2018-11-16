#include "verify_encoding.h"

#include <util/arith_tools.h>

//#include <langapi/language_util.h>

void verify_encodingt::check_function_bodies(
  const functionst &functions)
{
  for(const auto &f : functions)
  {
    const auto &signature = to_mathematical_function_type(f.first.type());
    check_function_body(signature, f.second);
    if(f.second.type()!=signature.codomain())
    {
      throw "function body has wrong type";
    }
  }
}

void verify_encodingt::check_function_body(
  const mathematical_function_typet &signature,
  const exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(expr).get_identifier();
    static const std::string parameter_prefix="synth::parameter";

    if(std::string(id2string(identifier), 0, parameter_prefix.size())==parameter_prefix)
    {
      std::string suffix(id2string(identifier), parameter_prefix.size(), std::string::npos);
      std::size_t count=std::stoul(suffix);
      const auto &parameters=signature.domain();
      if(count>=parameters.size())
      {
        throw "invalid parameter in function body: "+
              id2string(identifier);
      }

      if(expr.type()!=parameters[count].type())
      {
        throw "parameter with invalid type in function body: "+
              id2string(identifier);
      }
    }
    else
    {
      throw "unexpected symbol in function body: "+
            id2string(identifier);
    }
  }
  else
  {
    for(const auto &op : expr.operands())
      check_function_body(signature, op);
  }
}

exprt verify_encodingt::operator()(const exprt &expr) const
{
  if(expr.id()==ID_function_application)
  {
    const auto &e=to_function_application_expr(expr);

    auto f_it=functions.find(e.function());
    
    exprt result=f_it==functions.end()?
      from_integer(0, e.type()):f_it->second;

    // need to instantiate parameters with arguments
    exprt instance=instantiate(result, e);

    return instance;
  }
  else
  {
    exprt tmp=expr;

    for(auto &op : tmp.operands())
      op=(*this)(op);

    return tmp;
  }
}

exprt verify_encodingt::instantiate(
  const exprt &expr,
  const function_application_exprt &e) const
{
  if(expr.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(expr).get_identifier();
    static const std::string parameter_prefix="synth::parameter";

    if(std::string(id2string(identifier), 0, parameter_prefix.size())==parameter_prefix)
    {
      std::string suffix(id2string(identifier), parameter_prefix.size(), std::string::npos);
      std::size_t count=std::stoul(suffix);
      assert(count<e.arguments().size());
      return e.arguments()[count];
    }
    else
      return expr;
  }
  else
  {
    exprt tmp=expr;

    for(auto &op : tmp.operands())
      op=instantiate(op, e);

    return tmp;
  }
}

#include <iostream>
counterexamplet verify_encodingt::get_counterexample(
  const decision_proceduret &solver) const
{
  counterexamplet result;

  // iterate over nondeterministic symbols, and get their value
  for(const auto &var : free_variables)
  {
    exprt value=solver.get(var);
    result.assignment[var]=value;
    if(value==nil_exprt() && var.id()==ID_nondet_symbol)
    {
      nondet_symbol_exprt tmp_var=to_nondet_symbol_expr(var);
      tmp_var.set_identifier("nondet_"+id2string(to_nondet_symbol_expr(var).get_identifier()));
      value=solver.get(tmp_var);
      result.assignment[var]=value;
    }
    if(value==nil_exprt())
    {
      std::cout << "Warning: unable to find value for "<< var.pretty()<<std::endl;
      result.assignment[var] = constant_exprt("0", var.type());
      std::cout<<"Assume has been simplified out by solver.\n" <<std::endl;
    }
  }

  return result;
}

