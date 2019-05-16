#include "fourier_motzkin.h"

#include <util/arith_tools.h>

#include <langapi/language_util.h>

#include <algorithm>

exprt fourier_motzkint::get_result() const
{
  std::set<exprt> disjunct_set;
  std::vector<exprt> unique_disjuncts;

  for(const auto &d : result_disjuncts)
  {
    if(disjunct_set.insert(d).second)
      unique_disjuncts.push_back(d);
  }

  return disjunction(unique_disjuncts);
}

literalt fourier_motzkint::convert_rest(const exprt &expr)
{
  // record
  if(expr.id()==ID_lt || expr.id()==ID_le ||
     expr.id()==ID_gt || expr.id()==ID_ge)
  {
    record_ite(expr);
    literalt l=prop.new_variable();
    constraints.push_back(constraintt(l, expr));
    return l;
  }
  else if(expr.id()==ID_equal || expr.id()==ID_notequal)
  {
    // numeric?
    assert(expr.operands().size()==2);

    const typet &t=expr.op0().type();
    if(t.id()==ID_signedbv ||
       t.id()==ID_unsignedbv ||
       t.id()==ID_integer ||
       t.id()==ID_real)
    {
      // need to split into <=, >=, i.e., x=y <-> x<=y && x>=y
      literalt l_le, l_ge;

      l_le=convert(binary_predicate_exprt(expr.op0(), ID_le, expr.op1())),
      l_ge=convert(binary_predicate_exprt(expr.op0(), ID_ge, expr.op1()));

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
  else
  {
    // ignore
    return prop.new_variable();
  }
}

void fourier_motzkint::record_ite(const exprt &src)
{
  for(const auto &op : src.operands())
    record_ite(op);

  if(src.id()==ID_if)
  {
    convert(to_if_expr(src).cond());
  }
}

exprt fourier_motzkint::remove_ite(const exprt &src)
{
  exprt tmp=src;

  for(auto &op : tmp.operands())
    op=remove_ite(op);

  if(tmp.id()==ID_if)
  {
    literalt l=convert(to_if_expr(tmp).cond());
    tvt t=prop.l_get(l);

    if(t.is_true())
      return to_if_expr(tmp).true_case();
    else
      return to_if_expr(tmp).false_case();
  }
  else
    return tmp;
}

void fourier_motzkint::rowt::negate()
{
  // ! (x<b) <--> (x>=b) <--> (-x<=-b)
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
  else if(addends.size()==1)
  {
    if(addends.front().expr.type().id()==ID_unsignedbv)
    {
      // these cannot be negative
      mp_integer b=bound;
      if(addends.front().negative)
        b.negate();

      if(is_strict) // 0 <= x < b
        return b<=0;
      else // 0 <= x <= b
        return b<0;
    }
    else
      return false;
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
    auto const_int = numeric_cast<mp_integer>(to_constant_expr(src));
    if(!const_int.has_value())
      failed=true;
    else
    {
      // constants go to the right hand side of the inequality
      if(!negate) const_int.value().negate();
      bound+=const_int.value();
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

exprt fourier_motzkint::addendt::as_expr() const
{
  if(negative)
    return unary_minus_exprt(expr);
  else
    return expr;
}

exprt fourier_motzkint::rowt::as_expr() const
{
  if(is_inconsistent())
    return false_exprt();
  else if(is_tautology())
    return true_exprt();
  else
  {
    assert(!addends.empty());
    if(addends.size()==1)
    {
      if(addends.front().negative)
      {
        exprt lhs=addends.front().expr;
        exprt rhs=from_integer(-bound, lhs.type());
        return binary_predicate_exprt(lhs, is_strict?ID_gt:ID_ge, rhs);
      }
      else
      {
        exprt lhs=addends.front().expr;
        exprt rhs=from_integer(bound, lhs.type());
        return binary_predicate_exprt(lhs, is_strict?ID_lt:ID_le, rhs);
      }
    }
    else
    {
      exprt::operandst ops;

      for(const auto &a : addends)
        ops.push_back(a.as_expr());

      plus_exprt lhs(ops, ops.front().type());

      exprt rhs=from_integer(bound, lhs.type());
      return binary_predicate_exprt(lhs, is_strict?ID_lt:ID_le, rhs);
    }
  }
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

fourier_motzkint::resultt fourier_motzkint::eliminate(
  const exprt &x,
  std::list<rowt> &rows)
{
  // collect the lower and upper bounds on 'x'
  std::list<rowt> lower_bounds, upper_bounds, unrelated;

  for(const auto &r : rows)
  {
    log.debug() << "FM BOUND: " << as_string(r) << messaget::eom;
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
          log.debug() << "FM LOWER: " << as_string(new_r)
                      << (r.bound>0 || new_r.empty()?"":"+") << -r.bound
                      << (r.is_strict?" < ":" <= ") << from_expr(ns, "", x) << messaget::eom;
        else
        {
          negate(new_r);
          log.debug() << "FM UPPER: " << from_expr(ns, "", x)
                      << (r.is_strict?" < ":" <= ") << as_string(new_r)
                      << (r.bound.is_negative() || new_r.empty()?"":"+") << r.bound << messaget::eom;
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
      log.debug() << "FM NEW:   " << as_string(new_row) << messaget::eom;
    }

  for(const auto &r : unrelated)
    log.debug() << "FM UNREL: " << as_string(r) << messaget::eom;

  for(const auto &r : new_rows)
    if(r.is_inconsistent())
    {
      log.debug() << "FM INCONSISTENT" << messaget::eom;
      return resultt::D_UNSATISFIABLE;
    }

  for(const auto &r : unrelated)
    new_rows.push_back(r);

  if(new_rows.empty())
    log.debug() << "FM CONSISTENT (TAUTOLOGY)" << messaget::eom;
  else
    log.debug() << "FM CONSISTENT" << messaget::eom;

  // subsumption check
  subsumption(new_rows);

  for(const auto &r : new_rows)
    log.debug() << "FM FINAL: " << as_string(r) << messaget::eom;

  rows.swap(new_rows);

  return resultt::D_SATISFIABLE;
}

void fourier_motzkint::get_variables(const exprt &src)
{
  for(const auto &op : src.operands())
    get_variables(op);

  if(src.id()==ID_symbol)
  {
    if(src.type().id()!=ID_bool)
      variables.insert(src);
  }
}

void fourier_motzkint::eliminate()
{
  for(const auto &c : constraints)
    get_variables(c.expr);

  std::list<rowt> rows;

  for(const auto &c : constraints)
  {
    tvt value=prop.l_get(c.l);
    if(value.is_unknown())
      continue;

    exprt tmp=remove_ite(c.expr);

    rowt r(tmp);
    if(!r)
    {
      if(value.is_false())
        r.negate();

      r.eliminate_strict();
      r.normalize();

      rows.push_back(r);
    }
  }

  // first do the existential ones
  for(const auto &x : existential_variables)
  {
    log.debug() << "FM x='" << from_expr(ns, "", x) << '\'' << messaget::eom;

    auto result=eliminate(x, rows);

    if(result==resultt::D_UNSATISFIABLE)
      return;
  }

  // remember what we have now
  auto projection_result=rows;

  // run a bit more, in case the rest is inconsistent
  for(const auto &x : variables)
  {
    if(existential_variables.find(x)!=existential_variables.end())
      continue; // done already

    log.debug() << "FM x='" << from_expr(ns, "", x) << '\'' << messaget::eom;

    auto result=eliminate(x, rows);

    if(result==resultt::D_UNSATISFIABLE)
      return;
  }

  log.debug() << "FM DONE!" << messaget::eom;

  exprt::operandst conjuncts;
  for(const auto &r: projection_result)
    conjuncts.push_back(r.as_expr());

  result_disjuncts.push_back(conjunction(conjuncts));
}

void fourier_motzkint::assignment()
{
  for(const auto &c : constraints)
  {
    tvt value=prop.l_get(c.l);

    exprt tmp=remove_ite(c.expr);

    log.debug() << "FM ";
    log.debug().width(9);
    log.debug() << std::left << std::string(value.to_string())+": "
            << from_expr(ns, "", tmp) << messaget::eom;
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

    log.status() << "******** DPLL(FM) iteration " << iteration << messaget::eom;
    propt::resultt result=prop.prop_solve();

    switch(result)
    {
    case propt::resultt::P_SATISFIABLE:
      assignment();
      break; // next iteration

    case propt::resultt::P_UNSATISFIABLE:
      return resultt::D_UNSATISFIABLE;

    default:
    case propt::resultt::P_ERROR:
      return resultt::D_ERROR;
    }
  }
}

