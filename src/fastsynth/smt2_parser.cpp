/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2_parser.h"

#include <util/arith_tools.h>

void new_smt2_parsert::command_sequence()
{
  while(next_token()==OPEN)
  {
    if(next_token()!=SYMBOL)
    {
      error() << "expected symbol as command" << eom;
      return;
    }

    command(buffer);

    switch(next_token())
    {
    case END_OF_FILE:
      error() << "expected closing parenthesis at end of command, but got EOF" << eom;
      return;

    case CLOSE:
      // what we expect
      break;

    default:
      error() << "expected end of command" << eom;
      return;
    }
  }

  if(token!=END_OF_FILE)
  {
    error() << "unexpected token in command sequence" << eom;
  }
}

void new_smt2_parsert::ignore_command()
{
  std::size_t parentheses=0;
  while(true)
  {
    switch(peek())
    {
    case OPEN:
      next_token();
      parentheses++;
      break;

    case CLOSE:
      if(parentheses==0)
        return; // done

      next_token();
      parentheses--;
      break;

    case END_OF_FILE:
      error() << "unexpected EOF in command" << eom;
      return;

    default:
      next_token();
    }
  }
}
exprt::operandst new_smt2_parsert::operands()
{
  exprt::operandst result;

  while(peek()!=CLOSE)
    result.push_back(expression());

  next_token(); // eat the ')'

  return result;
}

exprt new_smt2_parsert::let_expression()
{
  if(next_token()!=OPEN)
  {
    error() << "expected bindings after let" << eom;
    return nil_exprt();
  }

  std::vector<std::pair<irep_idt, exprt>> bindings;

  while(peek()==OPEN)
  {
    next_token();

    if(next_token()!=SYMBOL)
    {
      error() << "expected symbol in binding" << eom;
      return nil_exprt();
    }

    irep_idt identifier=buffer;

    // note that the previous bindings are _not_ visible yet
    exprt value=expression();

    if(next_token()!=CLOSE)
    {
      error() << "expected ')' after value in binding" << eom;
      return nil_exprt();
    }

    bindings.push_back(
      std::pair<irep_idt, exprt>(identifier, value));
  }

  if(next_token()!=CLOSE)
  {
    error() << "expected ')' at end of bindings" << eom;
    return nil_exprt();
  }

  // go forwards, add to scope
  for(const auto &b : bindings)
  {
    id_stack.push_back(id_mapt());
    auto &entry=id_stack.back()[b.first];
    entry.type=b.second.type();
    entry.definition=b.second;
  }

  exprt expr=expression();

  if(next_token()!=CLOSE)
  {
    error() << "expected ')' after let" << eom;
    return nil_exprt();
  }

  exprt result=expr;

  // go backwards
  for(auto r_it=bindings.rbegin(); r_it!=bindings.rend(); r_it++)
  {
    let_exprt let;
    let.symbol()=symbol_exprt(r_it->first, r_it->second.type());
    let.value()=r_it->second;
    let.where().swap(result);
    result=let;
    id_stack.pop_back();
  }

  return result;
}

exprt new_smt2_parsert::quantifier_expression(irep_idt id)
{
  if(next_token()!=OPEN)
  {
    error() << "expected bindings after " << id << eom;
    return nil_exprt();
  }

  std::vector<symbol_exprt> bindings;

  while(peek()==OPEN)
  {
    next_token();

    if(next_token()!=SYMBOL)
    {
      error() << "expected symbol in binding" << eom;
      return nil_exprt();
    }

    irep_idt identifier=buffer;

    typet type=sort();

    if(next_token()!=CLOSE)
    {
      error() << "expected ')' after sort in binding" << eom;
      return nil_exprt();
    }

    bindings.push_back(symbol_exprt(identifier, type));
  }

  if(next_token()!=CLOSE)
  {
    error() << "expected ')' at end of bindings" << eom;
    return nil_exprt();
  }

  // go forwards, add to scope
  for(const auto &b : bindings)
  {
    id_stack.push_back(id_mapt());
    auto &entry=id_stack.back()[b.get_identifier()];
    entry.type=b.type();
    entry.definition=nil_exprt();
  }

  exprt expr=expression();

  if(next_token()!=CLOSE)
  {
    error() << "expected ')' after " << id << eom;
    return nil_exprt();
  }

  exprt result=expr;

  // go backwards
  for(auto r_it=bindings.rbegin(); r_it!=bindings.rend(); r_it++)
  {
    binary_predicate_exprt quantifier(id);
    quantifier.op0()=*r_it;
    quantifier.op1().swap(result);
    result=quantifier;
    id_stack.pop_back();
  }

  return result;
}

exprt new_smt2_parsert::function_application(
  const irep_idt &identifier,
  const exprt::operandst &op)
{
  #if 0
  const auto &f = id_map[identifier];

  function_application_exprt result;

  result.function()=symbol_exprt(identifier, f.type);
  result.arguments()=op;

  // check the arguments
  if(op.size()!=f.type.variables().size())
  {
    error() << "wrong number of arguments for function" << eom;
    return nil_exprt();
  }

  for(std::size_t i=0; i<op.size(); i++)
  {
    if(op[i].type() != f.type.variables()[i].type())
    {
      error() << "wrong type for arguments for function" << eom;
      return result;
    }
  }

  result.type()=f.type.range();
  return result;
  #endif
  return nil_exprt();
}

exprt new_smt2_parsert::cast_bv_to_signed(const exprt &expr)
{
  if(expr.type().id()==ID_signedbv) // no need to cast
    return expr;

  if(expr.type().id()!=ID_unsignedbv)
  {
    error() << "expected unsigned bitvector" << eom;
    return expr;
  }

  auto width=to_unsignedbv_type(expr.type()).get_width();
  signedbv_typet signed_type(width);

  typecast_exprt result(expr, signed_type);
  result.op0()=expr;
  result.type()=signed_type;

  return result;
}

exprt new_smt2_parsert::cast_bv_to_unsigned(const exprt &expr)
{
  if(expr.type().id()==ID_unsignedbv) // no need to cast
    return expr;

  if(expr.type().id()!=ID_signedbv)
  {
    error() << "expected signed bitvector" << eom;
    return expr;
  }

  auto width=to_signedbv_type(expr.type()).get_width();
  unsignedbv_typet unsigned_type(width);

  typecast_exprt result(expr, unsigned_type);
  result.op0()=expr;
  result.type()=unsigned_type;

  return result;
}

exprt new_smt2_parsert::multi_ary(irep_idt id, exprt::operandst &op)
{
  if(op.empty())
  {
    error() << "expression must have at least one operand" << eom;
    return nil_exprt();
  }
  else
  {
    for(std::size_t i=1; i<op.size(); i++)
    {
      if(op[i].type()!=op[0].type())
      {
        error() << "expression must have operands with matching types" << eom;
        return nil_exprt();
      }
    }

    exprt result(id, op[0].type());
    result.operands().swap(op);
    return result;
  }
}

exprt new_smt2_parsert::binary_predicate(irep_idt id, exprt::operandst &op)
{
  if(op.size()!=2)
  {
    error() << "expression must have two operands" << eom;
    return nil_exprt();
  }
  else
  {
    if(op[0].type()!=op[1].type())
    {
      error() << "expression must have operands with matching types" << eom;
      return nil_exprt();
    }

    return binary_predicate_exprt(op[0], id, op[1]);
  }
}

exprt new_smt2_parsert::unary(irep_idt id, exprt::operandst &op)
{
  if(op.size()!=1)
  {
    error() << "expression must have one operand" << eom;
    return nil_exprt();
  }
  else
    return unary_exprt(id, op[0], op[0].type());
}

exprt new_smt2_parsert::binary(irep_idt id, exprt::operandst &op)
{
  if(op.size()!=2)
  {
    error() << "expression must have two operands" << eom;
    return nil_exprt();
  }
  else
  {
    if(op[0].type()!=op[1].type())
    {
      error() << "expression must have operands with matching types" << eom;
      return nil_exprt();
    }

    return binary_exprt(op[0], id, op[1], op[0].type());
  }
}

exprt new_smt2_parsert::expression()
{
  switch(next_token())
  {
  case SYMBOL:
    {
      // hash it
      const irep_idt identifier=buffer;

      if(identifier==ID_true)
        return true_exprt();
      else if(identifier==ID_false)
        return false_exprt();
      else
      {
        // rummage through stack of IDs
        for(auto r_it=id_stack.rbegin();
            r_it!=id_stack.rend();
            r_it++)
        {
          auto id_it=r_it->find(identifier);
          if(id_it!=r_it->end())
            return symbol_exprt(identifier, id_it->second.type);
        }

        error() << "unknown symbol " << identifier << eom;
        return nil_exprt();
      }
    }

  case NUMERAL:
    if(buffer.size()>=2 && buffer[0]=='#' && buffer[1]=='x')
    {
      mp_integer value=
        string2integer(std::string(buffer, 2, std::string::npos), 16);
      const std::size_t width = 4*(buffer.length() - 2);
      CHECK_RETURN(width!=0 && width%4==0);
      unsignedbv_typet type(width);
      return from_integer(value, type);
    }
    else if(buffer.size()>=2 && buffer[0]=='#' && buffer[1]=='b')
    {
      mp_integer value=
        string2integer(std::string(buffer, 2, std::string::npos), 2);
      const std::size_t width = buffer.size() - 2;
      CHECK_RETURN(width!=0 && width%2==0);
      unsignedbv_typet type(width);
      return from_integer(value, type);
    }
    else
    {
      return constant_exprt(buffer, integer_typet());
    }

  case OPEN:
    if(next_token()==SYMBOL)
    {
      // hash it
      const irep_idt id=buffer;

      if(id==ID_let)
      {
        return let_expression();
      }
      else if(id==ID_forall || id==ID_exists)
      {
        return quantifier_expression(id);
      }

      if(id=="_")
      {
        // indexed identifier
        if(next_token()!=SYMBOL)
        {
          error() << "expected symbol after '_'" << eom;
          return nil_exprt();
        }

        if(has_prefix(buffer, "bv"))
        {
          mp_integer i=string2integer(std::string(buffer, 2, std::string::npos));

          if(next_token()!=NUMERAL)
          {
            error() << "expected numeral as bitvector literal width" << eom;
            return nil_exprt();
          }

          auto width=std::stoll(buffer);

          if(next_token()!=CLOSE)
          {
            error() << "expected ')' after bitvector literal" << eom;
            return nil_exprt();
          }

          return from_integer(i, unsignedbv_typet(width));
        }
        else if(id=="extract")
        {
          if(next_token()!=NUMERAL)
          {
            error() << "expected numeral after extract" << eom;
            return nil_exprt();
          }

          auto upper=std::stoll(buffer);

          if(next_token()!=NUMERAL)
          {
            error() << "expected two numerals after extract" << eom;
            return nil_exprt();
          }

          auto lower=std::stoll(buffer);

          if(next_token()!=CLOSE)
          {
            error() << "expected ')' after extract" << eom;
            return nil_exprt();
          }

          auto upper_e=from_integer(upper, integer_typet());
          auto lower_e=from_integer(lower, integer_typet());

          auto op=expression();
          unsignedbv_typet t(upper-lower+1);

          return extractbits_exprt(op, upper_e, lower_e, t);
        }
        else
        {
          error() << "unknown indexed identifier " << buffer << eom;
          return nil_exprt();
        }
      }
      else
      {
        auto op=operands();

        if(id==ID_and ||
           id==ID_or ||
           id==ID_xor)
        {
          return multi_ary(id, op);
        }
        else if(id==ID_not)
        {
          return unary(id, op);
        }
        else if(id==ID_equal ||
                id==ID_le ||
                id==ID_ge ||
                id==ID_lt ||
                id==ID_gt)
        {
          return binary_predicate(id, op);
        }
        else if(id=="bvule")
        {
          return binary_predicate(ID_le, op);
        }
        else if(id=="bvsle")
        {
          op[0]=cast_bv_to_signed(op[0]);
          op[1]=cast_bv_to_signed(op[1]);
          return binary_predicate(ID_le, op);
        }
        else if(id=="bvuge")
        {
          return binary_predicate(ID_ge, op);
        }
        else if(id=="bvsge")
        {
          op[0]=cast_bv_to_signed(op[0]);
          op[1]=cast_bv_to_signed(op[1]);
          return binary_predicate(ID_ge, op);
        }
        else if(id=="bvult")
        {
          return binary_predicate(ID_lt, op);
        }
        else if(id=="bvslt")
        {
          op[0]=cast_bv_to_signed(op[0]);
          op[1]=cast_bv_to_signed(op[1]);
          return binary_predicate(ID_lt, op);
        }
        else if(id=="bvugt")
        {
          return binary_predicate(ID_gt, op);
        }
        else if(id=="bvsgt")
        {
          op[0]=cast_bv_to_signed(op[0]);
          op[1]=cast_bv_to_signed(op[1]);
          return binary_predicate(ID_gt, op);
        }
        else if(id=="bvashr")
        {
          op[0]=cast_bv_to_signed(op[0]);
          op[1]=cast_bv_to_signed(op[1]);
          return cast_bv_to_unsigned(binary(ID_shr, op));
        }
        else if(id=="bvlshr" || id=="bvshr")
        {
          return binary(ID_shr, op);
        }
        else if(id=="bvlshr" || id=="bvashl" || id=="bvshl")
        {
          return binary(ID_shl, op);
        }
        else if(id=="bvand")
        {
          return multi_ary(ID_bitand, op);
        }
        else if(id=="bvor")
        {
          return multi_ary(ID_bitor, op);
        }
        else if(id=="bvxor")
        {
          return multi_ary(ID_bitxor, op);
        }
        else if(id=="bvnot")
        {
          return unary(ID_bitnot, op);
        }
        else if(id=="bvneg")
        {
          return unary(ID_unary_minus, op);
        }
        else if(id=="bvadd")
        {
          return multi_ary(ID_plus, op);
        }
        else if(id==ID_plus)
        {
          return multi_ary(id, op);
        }
        else if(id=="bvsub" || id=="-")
        {
          return binary(ID_minus, op);
        }
        else if(id=="bvmul" || id=="*")
        {
          return binary(ID_mult, op);
        }
        else if(id=="bvsdiv")
        {
          op[0]=cast_bv_to_signed(op[0]);
          op[1]=cast_bv_to_signed(op[1]);
          return cast_bv_to_unsigned(binary(ID_div, op));
        }
        else if(id=="bvudiv")
        {
          return binary(ID_div, op);
        }
        else if(id=="/" || id=="div")
        {
          return binary(ID_div, op);
        }
        else if(id=="bvsrem")
        {
          op[0]=cast_bv_to_signed(op[0]);
          op[1]=cast_bv_to_signed(op[1]);
          return cast_bv_to_unsigned(binary(ID_mod, op));
        }
        else if(id=="bvurem" || id=="%")
        {
          return binary(ID_mod, op);
        }
        else if(id=="concat")
        {
          if(op.size()!=2)
          {
            error() << "concat takes three operands" << eom;
            return nil_exprt();
          }

          auto width0=to_unsignedbv_type(op[0].type()).get_width();
          auto width1=to_unsignedbv_type(op[1].type()).get_width();

          unsignedbv_typet t(width0+width1);

          return binary_exprt(op[0], ID_concatenation, op[1], t);
        }
        else if(id=="ite")
        {
          if(op.size()!=3)
          {
            error() << "ite takes three operands" << eom;
            return nil_exprt();
          }

          if(op[0].type().id()!=ID_bool)
          {
            error() << "ite takes a boolean as first operand" << eom;
            return nil_exprt();
          }

          if(op[1].type()!=op[2].type())
          {
            error() << "ite needs matching types" << eom;
            return nil_exprt();
          }

          return if_exprt(op[0], op[1], op[2]);
        }
        else if(id=="=>" || id=="implies")
        {
          return binary(ID_implies, op);
        }
        else
        {
          // rummage through stack of IDs
          for(auto r_it=id_stack.rbegin();
              r_it!=id_stack.rend();
              r_it++)
          {
            auto id_it=r_it->find(id);
            if(id_it!=r_it->end())
            {
              return symbol_exprt(id, id_it->second.type);
            }
          }

          error() << "unknown symbol " << id << eom;
          return nil_exprt();
        }
      }
    }
    else
    {
      error() << "expected symbol after '(' in an expression" << eom;
      return nil_exprt();
    }

  case END_OF_FILE:
    error() << "EOF in an expression" << eom;
    return nil_exprt();

  default:
    error() << "unexpected token in an expression" << eom;
    return nil_exprt();
  }
}

typet new_smt2_parsert::sort()
{
  switch(next_token())
  {
  case SYMBOL:
    if(buffer=="Bool")
      return bool_typet();
    else if(buffer=="Int")
      return integer_typet();
    else if(buffer=="Real")
      return real_typet();
    else
    {
      error() << "unexpected sort: `" << buffer << '\'' << eom;
      return nil_typet();
    }

  case OPEN:
    if(next_token()!=SYMBOL)
    {
      error() << "expected symbol after '(' in a sort " << eom;
      return nil_typet();
    }

    if(buffer=="_")
    {
      // indexed identifier
      if(next_token()!=SYMBOL)
      {
        error() << "expected symbol after '_' in a sort" << eom;
        return nil_typet();
      }

      if(buffer=="BitVec")
      {
        if(next_token()!=NUMERAL)
        {
          error() << "expected numeral as bit-width" << eom;
          return nil_typet();
        }

        auto width=std::stoll(buffer);

        // eat the ')'
        if(next_token()!=CLOSE)
        {
          error() << "expected ')' at end of sort" << eom;
          return nil_typet();
        }

        return unsignedbv_typet(width);
      }
      else
      {
        error() << "unexpected sort: `" << buffer << '\'' << eom;
        return nil_typet();
      }
    }
    else
    {
      error() << "unexpected sort: `" << buffer << '\'' << eom;
      return nil_typet();
    }

  default:
    error() << "unexpected token in a sort " << buffer << eom;
    return nil_typet();
  }
}

typet new_smt2_parsert::function_signature_definition()
{
  if(next_token()!=OPEN)
  {
    error() << "expected '(' at beginning of signature" << eom;
    return nil_typet();
  }

  if(peek()==CLOSE)
  {
    next_token(); // eat the ')'
    return sort();
  }

  mathematical_function_typet result;

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

    auto &entry=id_stack.back()[id];
    entry.type=var.type();
    entry.definition=nil_exprt();

    if(next_token()!=CLOSE)
    {
      error() << "expected ')' at end of parameter" << eom;
      return result;
    }
  }

  next_token(); // eat the ')'

  result.codomain()=sort();

  return result;
}

typet new_smt2_parsert::function_signature_declaration()
{
  if(next_token()!=OPEN)
  {
    error() << "expected '(' at beginning of signature" << eom;
    return nil_typet();
  }

  if(peek()==CLOSE)
  {
    next_token(); // eat the ')'
    return sort();
  }

  mathematical_function_typet result;

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
    var.type()=sort();

    if(next_token()!=CLOSE)
    {
      error() << "expected ')' at end of parameter" << eom;
      return result;
    }
  }

  next_token(); // eat the ')'

  result.codomain()=sort();

  return result;
}

void new_smt2_parsert::command(const std::string &c)
{
  if(c=="declare-fun")
  {
    if(next_token()!=SYMBOL)
    {
      error() << "expected a symbol after declare-fun" << eom;
      ignore_command();
      return;
    }

    irep_idt id=buffer;

    if(id_stack.back().find(id)!=id_stack.back().end())
    {
      error() << "identifier `" << id << "' defined twice" << eom;
      ignore_command();
      return;
    }

    auto &entry=id_stack.back()[id];
    entry.type=function_signature_declaration();
    entry.definition=nil_exprt();
  }
  else if(c=="define-fun")
  {
    if(next_token()!=SYMBOL)
    {
      error() << "expected a symbol after define-fun" << eom;
      ignore_command();
      return;
    }

    const irep_idt id=buffer;

    if(id_stack.back().find(id)!=id_stack.back().end())
    {
      error() << "identifier `" << id << "' defined twice" << eom;
      ignore_command();
      return;
    }

    // create the entry
    id_stack.back()[id];

    id_stack.push_back(id_mapt());
    auto signature=function_signature_definition();
    exprt body=expression();
    id_stack.pop_back();

    auto &entry=id_stack.back()[id];
    entry.type=signature;
    entry.definition=body;
  }
  else
    ignore_command();
}
