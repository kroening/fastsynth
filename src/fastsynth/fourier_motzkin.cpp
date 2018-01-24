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
  is_strict=!is_strict;
  fourier_motzkint::negate(addends);
  bound.negate();
}

void fourier_motzkint::rowt::normalize()
{
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
  if(addends.empty())
  {
    if(is_strict) // 0 < b
      return bound<=0;
    else // 0 <= b
      return bound<0;
  }

  return false;
}

void fourier_motzkint::rowt::eliminate_strict()
{
  if(is_strict)
  {
    // integers only! X<b <=> X<=b-1
    is_strict=false;
    bound-=1;
  }
}

fourier_motzkint::rowt::rowt(const exprt &src):
  is_strict(false), failed(true)
{
  if(src.id()==ID_lt && src.operands().size()==2)
  {
    is_strict=true;
    collect_addends(src.op0(), false);
    collect_addends(src.op1(), true);
    failed=false;
  }
  else if(src.id()==ID_le && src.operands().size()==2)
  {
    is_strict=false;
    collect_addends(src.op0(), false);
    collect_addends(src.op1(), true);
    failed=false;
  }
  else if(src.id()==ID_gt && src.operands().size()==2)
  {
    is_strict=true;
    collect_addends(src.op0(), true);
    collect_addends(src.op1(), false);
    failed=false;
  }
  else if(src.id()==ID_ge && src.operands().size()==2)
  {
    is_strict=false;
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
  else if(src.id()==ID_constant)
  {
    mp_integer i;
    if(to_integer(src, i))
      failed=true;
    else
    {
      // constants go to the right hand side of the inequality
      if(!negate) i.negate();
      bound+=i;
    }
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

  if(r.is_strict)
    result+='<';
  else
    result+="<=";

  result+=' ';
  result+=integer2string(r.bound);

  return result;
}

void fourier_motzkint::subsumption(std::list<rowt> &rows)
{
  // delete tautologies
  for(auto r_it=rows.begin(); r_it!=rows.end();)
  {
    if(r_it->is_tautology())
      r_it=rows.erase(r_it);
    else
      r_it++;
  }

  std::map<addendst, mp_integer> smallest_bounds;

  for(const auto &r : rows)
  {
    auto b_it=smallest_bounds.find(r.addends);
    if(b_it==smallest_bounds.end())
      smallest_bounds[r.addends]=r.bound;
    else
      b_it->second=std::min(b_it->second, r.bound);
  }

  // delete subsumed ones
  for(auto r_it=rows.begin(); r_it!=rows.end();)
  {
    if(smallest_bounds[r_it->addends]==r_it->bound)
      r_it++; // strongest
    else
      r_it=rows.erase(r_it); // subsumed
  }
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

      r.eliminate_strict();
      r.normalize();

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
                    << (r.bound>0 || new_r.empty()?"":"+") << -r.bound
                    << (r.is_strict?" < ":" <= ") << from_expr(ns, "", x) << eom;
          else
          {
            negate(new_r);
            debug() << "FM UPPER: " << from_expr(ns, "", x)
                    << (r.is_strict?" < ":" <= ") << as_string(new_r)
                    << (r.bound.is_negative() || new_r.empty()?"":"+") << r.bound << eom;
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
        new_row.bound+=upper.bound;

        new_row.normalize();
        new_rows.push_back(new_row);
        debug() << "FM NEW:   " << as_string(new_row) << eom;
      }

    for(const auto &r : unrelated)
      debug() << "FM UNREL: " << as_string(r) << eom;

    for(const auto &r : new_rows)
      if(r.is_inconsistent())
      {
        debug() << "FM INCONSISTENT" << eom;
        return;
      }

    if(new_rows.empty())
      debug() << "FM TAUTOLOGY" << eom;
    else
    {
      debug() << "FM CONSISTENT" << eom;

      for(const auto &r : unrelated)
        new_rows.push_back(r);

      // subsumption check
      subsumption(new_rows);

      for(const auto &r : new_rows)
        debug() << "FM FINAL: " << as_string(r) << eom;
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

