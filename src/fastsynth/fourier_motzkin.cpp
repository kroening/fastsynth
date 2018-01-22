#include "fourier_motzkin.h"

#include <langapi/language_util.h>

literalt fourier_motzkint::convert_rest(const exprt &expr)
{
  // record
  literalt l=prop.new_variable();
  constraints.push_back(constraintt(l, expr));
  return l;
}

#if 0
exprt fourier_motzkint::drop_ite(const exprt &src)
{
  if(src.id()==ID_if)
  {
    return src;
  }
  else
  {
    exprt tmp=src;
    for(auto &op : tmp.operands())
      op=drop_ite(op);
    return tmp;
  }
}
#endif

void fourier_motzkint::boundt::flip()
{
  is_weak=!is_weak;
  negate(addends);
}

fourier_motzkint::boundt::boundt(const exprt &src):is_weak(false), failed(true)
{
  if(src.id()==ID_lt && src.operands().size()==2)
  {
    is_weak=true;
    collect_addends(src.op0(), false);
    collect_addends(src.op1(), true);
    failed=false;
  }
  else if(src.id()==ID_le && src.operands().size()==2)
  {
    is_weak=false;
    collect_addends(src.op0(), false);
    collect_addends(src.op1(), true);
    failed=false;
  }
  else if(src.id()==ID_gt && src.operands().size()==2)
  {
    is_weak=false;
    collect_addends(src.op0(), true);
    collect_addends(src.op1(), false);
    failed=false;
  }
  else if(src.id()==ID_ge && src.operands().size()==2)
  {
    is_weak=true;
    collect_addends(src.op0(), true);
    collect_addends(src.op1(), false);
    failed=false;
  }
  else
    failed=true;
}

void fourier_motzkint::boundt::collect_addends(
  const exprt &src,
  bool negate)
{
  if(src.id()==ID_plus)
  {
    for(const auto &op : src.operands())
      collect_addends(op, negate);
  }
  else if(src.id()==ID_unary_minus)
  {
    collect_addends(to_unary_minus_expr(src).op(), !negate);
  }
  else
  {
    addends.push_back(addendt());
    addends.back().expr=src;
    addends.back().negative=negate;
  }
}

std::vector<fourier_motzkint::addendt>::const_iterator
fourier_motzkint::boundt::find(const exprt &src) const
{
  for(auto it=addends.begin();
      it!=addends.end();
      it++)
  {
    if(it->expr==src)
      return it;
  }

  return addends.end();
}

std::string fourier_motzkint::as_string(const std::vector<addendt> &addends) const
{
  std::string result;

  bool first=true;
  for(const auto &a : addends)
  {
    if(first)
    {
      first=false;
      if(a.negative) result+='-';
    }
    else
    {
      if(a.negative)
        result+='-';
      else
        result+='+';
    }

    result+=from_expr(ns, "", a.expr);
  }

  return result;
}

std::string fourier_motzkint::as_string(const boundt &b) const
{
  std::string result=as_string(b.addends);

  result+=' ';

  if(b.is_weak)
    result+='<';
  else
    result+="<=";

  result+=" 0";

  return result;
}

void fourier_motzkint::eliminate()
{
  std::vector<boundt> bounds;

  for(const auto &c : constraints)
  {
    tvt value=prop.l_get(c.l);
    if(value.is_unknown())
      continue;

    boundt b(c.expr);
    if(!b)
    {
      if(value.is_false())
        b.flip();

      bounds.push_back(b);
    }
  }

  for(const auto &s : existential_variables)
  {
    debug() << "FM Eliminating: " << from_expr(ns, "", s) << eom;

    std::vector<addendt> lower_bound, upper_bound;

    for(const auto &b : bounds)
    {
      debug() << "FM BOUND: " << as_string(b) << eom;
      auto it=b.find(s);

      if(it!=b.end())
      {
        {
          std::vector<addendt> new_b;

          for(const auto &a : b.addends)
            if(a.expr!=s)
              new_b.push_back(a);

          if(it->negative)
            debug() << "FM LOWER: " << as_string(new_b)
                    << (b.is_weak?" < ":" <= ") << from_expr(ns, "", s) << eom;
          else
            debug() << "FM UPPER: " << from_expr(ns, "", s)
                    << (b.is_weak?" < ":" <= ") << as_string(new_b) << eom;
        }

        for(const auto &a : b.addends)
          if(a.expr!=s)
          {
            if(it->negative)
              lower_bound.push_back(a);
            else
              upper_bound.push_back(a);
          }
      }
    }
  }
}

void fourier_motzkint::assignment()
{
  for(const auto &c : constraints)
  {
    tvt value=prop.l_get(c.l);

    debug() << "FM ";
    debug().width(9);
    debug() << std::left << std::string(value.to_string())+": "
            << from_expr(ns, "", c.expr) << eom;
  }

  eliminate();
}

decision_proceduret::resultt fourier_motzkint::dec_solve()
{
  while(true)
  {
    propt::resultt result=prop.prop_solve();

    switch(result)
    {
    case propt::resultt::P_SATISFIABLE:
      assignment();
      return resultt::D_SATISFIABLE;

    case propt::resultt::P_UNSATISFIABLE:
      return resultt::D_UNSATISFIABLE;

    default:
      return resultt::D_ERROR;
    }
  }
}

