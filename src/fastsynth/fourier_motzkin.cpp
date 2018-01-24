#include "fourier_motzkin.h"

#include <util/arith_tools.h>

#include <langapi/language_util.h>

#include <algorithm>

literalt fourier_motzkint::convert_rest(const exprt &expr)
{
  // record
  if(expr.id()==ID_lt || expr.id()==ID_le ||
     expr.id()==ID_gt || expr.id()==ID_ge)
  {
    literalt l=prop.new_variable();
    constraints.push_back(constraintt(l, expr));
    return l;
  }
  else if(expr.id()==ID_equal || expr.id()==ID_notequal)
  {
    // need to split into <=, >=, i.e., x=y <-> x<=y && x>=y
    literalt l_le, l_ge;

    l_le=convert_rest(binary_predicate_exprt(expr.op0(), ID_le, expr.op1())),
    l_ge=convert_rest(binary_predicate_exprt(expr.op0(), ID_ge, expr.op1()));

    literalt l_equal=prop.land(l_le, l_ge);

    // one of them is always true
    prop.lcnf(l_le, l_ge);

    return expr.id()==ID_equal?l_equal:!l_equal;
  }
  else
  {
    // ignore
    return prop.new_variable();
  }
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

void fourier_motzkint::rowt::negate()
{
  is_weak=!is_weak;
  fourier_motzkint::negate(addends);
}

void fourier_motzkint::collate(std::vector<addendt> &addends)
{
  // constants
  for(auto it1=addends.begin(); it1!=addends.end(); it1++)
  {
    if(it1->expr.is_constant())
    {
      mp_integer it1_i, it2_i, sum;
      to_integer(it1->expr, it1_i);
      if(it1->negative) it1_i.negate();
      sum=it1_i;

      for(auto it2=std::next(it1); it2!=addends.end(); it2++)
      {
        if(it2->expr.is_constant())
        {
          to_integer(it2->expr, it2_i);
          if(it2->negative) it2_i.negate();
          sum+=it2_i;
          it2->expr=from_integer(0, it2->expr.type());
        }
      }

      it1->negative=(sum<0);
      if(it1->negative) sum.negate();
      it1->expr=from_integer(sum, it1->expr.type());
      break; // done
    }
  }

  std::map<exprt, mp_integer> coefficients;

  for(const auto &a : addends)
  {
    mp_integer offset=a.negative?-1:1;
    coefficients[a.expr]+=offset;
  }

  // remove the ones with zero coefficient
  for(auto &a : addends)
  {
    if(coefficients[a.expr]==0)
      a.expr=from_integer(0, a.expr.type());
  }

  // remove zeros
  for(auto it=addends.begin(); it!=addends.end();)
  {
    if(it->expr.is_zero())
      it=addends.erase(it);
    else
      it++;
  }

  // sort
  std::sort(addends.begin(), addends.end(),
    [](const addendt &A, const addendt &B) { return A.expr<B.expr; });
}

bool fourier_motzkint::rowt::is_inconsistent() const
{
  // we assume that collate() has been run
  if(addends.size()==1 &&
     addends.front().expr.is_constant())
  {
    mp_integer i;
    to_integer(addends.front().expr, i);
    if(addends.front().negative) i.negate();
    if(i>0) return true;
  }

  return false;
}

void fourier_motzkint::rowt::eliminate_weak()
{
  if(is_weak)
  {
    // integers only! X<0 <=> X+1<=0
    typet t;
    if(!addends.empty())
      t=addends.front().expr.type();
    else
      t=integer_typet();

    is_weak=false;
    addends.push_back(addendt());
    addends.back().negative=false;
    addends.back().expr=from_integer(1, t);
  }
}

fourier_motzkint::rowt::rowt(const exprt &src):
  is_weak(false), failed(true)
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
    is_weak=true;
    collect_addends(src.op0(), true);
    collect_addends(src.op1(), false);
    failed=false;
  }
  else if(src.id()==ID_ge && src.operands().size()==2)
  {
    is_weak=false;
    collect_addends(src.op0(), true);
    collect_addends(src.op1(), false);
    failed=false;
  }
  else
    failed=true;
}

void fourier_motzkint::rowt::collect_addends(
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
fourier_motzkint::rowt::find(const exprt &src) const
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

std::string fourier_motzkint::as_string(const rowt &r) const
{
  std::string result;

  if(r.is_empty())
    result+="0";
  else
    result+=as_string(r.addends);

  result+=' ';

  if(r.is_weak)
    result+='<';
  else
    result+="<=";

  result+=' ';
  result+='0';

  return result;
}

void fourier_motzkint::eliminate()
{
  std::vector<rowt> rows;

  for(const auto &c : constraints)
  {
    tvt value=prop.l_get(c.l);
    if(value.is_unknown())
      continue;

    rowt r(c.expr);
    if(!r)
    {
      if(value.is_false())
        r.negate();

      r.eliminate_weak();
      collate(r.addends);

      rows.push_back(r);
    }
  }

  for(const auto &x : existential_variables)
  {
    debug() << "FM x='" << from_expr(ns, "", x) << '\'' << eom;

    // collect the lower and upper bounds on 'x'
    std::list<rowt> lower_bounds, upper_bounds, unrelated;

    for(const auto &r : rows)
    {
      debug() << "FM BOUND: " << as_string(r) << eom;
      auto it=r.find(x);

      if(it==r.end())
        unrelated.push_back(r);
      else
      {
        {
          std::vector<addendt> new_r;

          for(const auto &a : r.addends)
            if(a.expr!=x)
              new_r.push_back(a);

          if(it->negative)
            debug() << "FM LOWER: " << as_string(new_r)
                    << (r.is_weak?" < ":" <= ") << from_expr(ns, "", x) << eom;
          else
          {
            negate(new_r);
            debug() << "FM UPPER: " << from_expr(ns, "", x)
                    << (r.is_weak?" < ":" <= ") << as_string(new_r) << eom;
          }
        }

        if(it->negative)
          lower_bounds.push_back(r);
        else
          upper_bounds.push_back(r);
      }
    }

    std::list<rowt> new_rows;

    // now form new constraints,
    // considering all pairs of upper and lower bounds
    for(const auto &lower : lower_bounds)
      for(const auto &upper: upper_bounds)
      {
        rowt new_row=lower;
        for(const auto &a : upper.addends)
          new_row.addends.push_back(a);

        collate(new_row.addends);
        new_rows.push_back(new_row);
        debug() << "FM NEW:   " << as_string(new_row) << eom;
      }

    for(const auto &b : unrelated)
      debug() << "FM UNREL: " << as_string(b) << eom;

    for(const auto &b : new_rows)
      if(b.is_inconsistent())
      {
        debug() << "FM INCONSISTENT" << eom;
        return;
      }

    if(new_rows.empty())
      debug() << "FM TAUTOLOGY" << eom;
    else
      debug() << "FM CONSISTENT" << eom;
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

  // block it
  bvt blocking_clause;

  for(const auto &c : constraints)
  {
    tvt value=prop.l_get(c.l);
    if(value.is_unknown())
      continue;

    if(value.is_true())
      blocking_clause.push_back(!c.l);
    else
      blocking_clause.push_back(c.l);
  }

  prop.lcnf(blocking_clause);
}

decision_proceduret::resultt fourier_motzkint::dec_solve()
{
  unsigned iteration=0;

  while(true)
  {
    iteration++;

    status() << "******** DPLL(FM) iteration " << iteration << eom;
    propt::resultt result=prop.prop_solve();

    switch(result)
    {
    case propt::resultt::P_SATISFIABLE:
      assignment();
      break; // next iteration

    case propt::resultt::P_UNSATISFIABLE:
      return resultt::D_UNSATISFIABLE;

    default:
      return resultt::D_ERROR;
    }
  }
}

