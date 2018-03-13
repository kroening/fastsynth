#include "sygus_parser.h"

#include <util/bv_arithmetic.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/replace_symbol.h>
#include <util/arith_tools.h>

#include <cctype>
#include <cassert>
#include <fstream>

void sygus_parsert::command_sequence()
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

void sygus_parsert::ignore_command()
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
exprt::operandst sygus_parsert::operands()
{
  exprt::operandst result;

  while(peek()!=CLOSE)
    result.push_back(expression());

  next_token(); // eat the ')'

  return result;
}

let_exprt sygus_parsert::let_expression(bool first_in_chain)
{
  let_exprt result;
  let_counter++;

  if(peek()!=OPEN && !first_in_chain)
  {
    // no need for chaining, single let exprt.
    result.operands()=operands();
    return result;
  }
  else
  {
    if(peek()==OPEN && first_in_chain)
    {
      next_token(); // eat the '('that starts the bindings list
    }

    next_token(); // eat the '(' that starts the next binding

    // get the symbol that is bound
    if(next_token()==SYMBOL)
    {
      result.symbol() = symbol_exprt(buffer, sort());
    }
    else
    {
      error() << "expected symbol in let expression" << eom;
      return result;
    }

    // get value
    result.value() = expression();
    next_token(); // eat the ')' that closes this binding

    // now rename op0 -- this really happens at the very
    // end of the let, but that's hard with recursion
    irep_idt old_id=result.symbol().get_identifier();
    irep_idt new_id=id2string(old_id)+
                    '#'+std::to_string(id_counter++)+
                    'L'+std::to_string(let_counter++);

    result.symbol().set_identifier(new_id);
    let_variable_map[new_id]=result.value().type();
    full_let_variable_map[new_id]=result.value().type();
    renaming_map[old_id]=new_id;

    if(peek()!=CLOSE) // we are still in a chain of bindings
    {
      // get op2
      result.where() = let_expression(false);
      result.type() = result.where().type();
    }
    else
    {
      // we are at the end of the chain
      next_token(); // eat the ')' that closes the bindings list

      if(peek()!=OPEN)
      {
        error() << "let expects where here" << eom;
        return result;
      }

      result.where() = expression();
      result.type()=result.where().type();
      next_token(); // eat the final ')' that closes the let exprt
    }

    // don't rename any longer
    renaming_map.erase(old_id);
    let_variable_map.clear();
  }
  return result;
}

exprt sygus_parsert::function_application(
  const irep_idt &identifier,
  const exprt::operandst &op)
{
  const auto &f = function_map[identifier];

  function_application_exprt result;

  result.function()=symbol_exprt(identifier, f.type);
  result.arguments()=op;

  // check the arguments
  if(op.size()!=f.type.domain().size())
  {
    error() << "wrong number of arguments for function" << eom;
    return nil_exprt();
  }

  for(std::size_t i=0; i<op.size(); i++)
  {
    if(op[i].type() != f.type.domain()[i].type())
    {
      error() << "wrong type for arguments for function" << eom;
      return result;
    }
  }

  result.type()=f.type.codomain();
  return result;
}


void sygus_parsert::fix_ite_operation_result_type(if_exprt &expr)
{
  if(expr.op0().id()!=ID_bool)
    expr.op0().type()=bool_typet();

  if(expr.op1().type()!=expr.op2().type())
  {
   // default type is unsigned bitvector
    if(expr.op1().type().id()==ID_unsignedbv)
      expr.op2().type()=expr.op1().type();
    else if(expr.op1().type().id()==ID_unsignedbv)
      expr.op1().type()=expr.op2().type();
    else if(expr.op1().type().id()==ID_signedbv)
    {
      unsignedbv_typet type(to_signedbv_type(expr.op1().type()).get_width());
      expr.op1().type()=type;
      expr.op2().type()=type;
    }
    else if(expr.op2().type().id()==ID_signedbv)
    {
      unsignedbv_typet type(to_signedbv_type(expr.op2().type()).get_width());
      expr.op1().type()=type;
      expr.op2().type()=type;
    }

    // throw error if still mismatching. Could be because bitvector widths are different
    if(expr.op1().type()!=expr.op2().type())
    {
      error() << "mismatching types for ite operand" << eom;
    }
  }

  expr.type()=expr.op1().type();
}

void sygus_parsert::fix_binary_operation_operand_types(exprt &expr)
{
  // TODO: deal with different widths of bitvector
  if(expr.operands().size()!=2)
  {
    error() << "two operands expected for binary operation " << expr.id() << eom;
    return;
  }

  if(expr.op0().type()!=expr.op1().type())
  {
    // default type is unsigned bitvector
    if(expr.op0().type().id()==ID_unsignedbv)
      expr.op1().type()=expr.op0().type();
    else if(expr.op1().type().id()==ID_unsignedbv)
      expr.op0().type()=expr.op1().type();
    else if(expr.op0().type().id()==ID_signedbv)
    {
      unsignedbv_typet type(to_signedbv_type(expr.op0().type()).get_width());
      expr.op0().type()=type;
      expr.op1().type()=type;
    }
    else if(expr.op1().type().id()==ID_signedbv)
    {
      unsignedbv_typet type(to_signedbv_type(expr.op1().type()).get_width());
      expr.op0().type()=type;
      expr.op1().type()=type;
    }

    // throw error if still mismatching. Could be because bitvector widths are different
    if(expr.op0().type()!=expr.op1().type())
    {
      error() << "mismatching types for binary operand" << expr.id() << eom;
    }
  }
}


exprt sygus_parsert::cast_bv_to_signed(exprt &expr)
{
  if(expr.type().id()==ID_signedbv) // no need to cast
    return expr;

  if(expr.type().id()!=ID_unsignedbv)
  {
    error() << "expected unsigned bitvector" << eom;
    return expr;
  }

 signedbv_typet signed_type(to_unsignedbv_type(expr.type()).get_width());
 typecast_exprt result(expr, signed_type);
 result.op0()=expr;
 result.type()=signed_type;

 return result;
}

exprt sygus_parsert::cast_bv_to_unsigned(exprt &expr)
{
  if(expr.type().id()==ID_unsignedbv) // no need to cast
    return expr;

  if(expr.type().id()!=ID_signedbv)
  {
    error() << "expected signed bitvector" << eom;
    return expr;
  }

  unsignedbv_typet unsigned_type(to_signedbv_type(expr.type()).get_width());
  typecast_exprt result(expr, unsigned_type);
  result.op0()=expr;
  result.type()=unsigned_type;
  return result;
}

static bool is_negative_numeral(const std::string &s)
{
  if(s.size()>=2 && s[0]=='-')
  {
    for(std::size_t i=1; i<s.size(); i++)
      if(!isdigit(s[i]))
        return false;

    return true;
  }
  else
    return false;
}

exprt sygus_parsert::expression()
{
  switch(next_token())
  {
  case SYMBOL:
    // sugys allows negative numerals "-1",
    // which are a SYMBOL in SMT-LIB2
    if(is_negative_numeral(buffer))
    {
      return constant_exprt(buffer, integer_typet());
    }
    else
    {
      // hash it
      irep_idt identifier=buffer;

      // renamed?
      const auto r_it=renaming_map.find(identifier);
      if(r_it!=renaming_map.end())
        identifier=r_it->second;

      if(identifier==ID_true)
        return true_exprt();
      else if(identifier==ID_false)
        return false_exprt();
      else if(local_variable_map.find(identifier)!=
              local_variable_map.end())
      {
        // search local variable map first, we clear the local variable map
        // as soon as we are done parsing the function body
        return symbol_exprt(identifier, local_variable_map[identifier]);
      }
      else if(variable_map.find(identifier)!=
              variable_map.end())
      {
        return symbol_exprt(identifier, variable_map[identifier]);
      }
      else if(let_variable_map.find(identifier)!=
          let_variable_map.end())
      {
        // search let variables, we clear let variables when done with parsing let
        return symbol_exprt(identifier, let_variable_map[identifier]);
      }
      else if(function_map.find(identifier)!=
              function_map.end())
      {
        return function_application(identifier, exprt::operandst());
      }
      else
      {
        error() << "unknown symbol " << buffer << eom;
        return symbol_exprt(identifier, bool_typet());
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
        // bool indicates first in chain
        return let_expression(true);
      }

      auto op=operands();

      if(id==ID_and)
      {
        and_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id==ID_or)
      {
        or_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id==ID_xor)
      {
        notequal_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id==ID_not)
      {
        not_exprt result;
        result.operands()=op;
        return result;
      }
      else if(id=="=")
      {
        equal_exprt result;
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=bool_typet();
        return result;
      }
      else if(id=="<=" || id=="bvule" || id=="bvsle")
      {
        predicate_exprt result(ID_le);
        result.operands()=op;

        fix_binary_operation_operand_types(result);
        result.type()=bool_typet();

        if(id=="bvsle")
        {
          result.op0()=cast_bv_to_signed(result.op0());
          result.op1()=cast_bv_to_signed(result.op1());
        }
        return result;
      }
      else if(id==">=" || id=="bvuge" || id=="bvsge")
      {
        predicate_exprt result(ID_ge);
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=bool_typet();

        if(id=="bvsge")
        {
          result.op0()=cast_bv_to_signed(result.op0());
          result.op1()=cast_bv_to_signed(result.op1());
        }

        return result;
      }
      else if(id=="<" || id=="bvult" || id=="bvslt")
      {
        predicate_exprt result(ID_lt);
        result.operands()=op;

        fix_binary_operation_operand_types(result);
        result.type()=bool_typet();

        if(id=="bvslt")
        {
          result.op0()=cast_bv_to_signed(result.op0());
          result.op1()=cast_bv_to_signed(result.op1());
        }
        return result;
      }
      else if(id==">" || id=="bvugt" || id=="bvsgt")
      {
        predicate_exprt result(ID_gt);
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=bool_typet();

        if(id=="bvsgt")
        {
          result.op0()=cast_bv_to_signed(result.op0());
          result.op1()=cast_bv_to_signed(result.op1());
        }
        return result;
      }
      else if(id=="bvashr")
      {
        if(op.size()!=2)
        {
          error() << "bit shift must have 2 operands" << eom;
          return nil_exprt();
        }

        ashr_exprt result(op[0], op[1]);
        result.type()=op[0].type();
        return result;
      }
      else if(id=="bvlshr" || id=="bvshr")
      {
        if(op.size()!=2)
        {
          error() << "bit shift must have two operands" << eom;
          return nil_exprt();
        }

        lshr_exprt result(op[0], op[1]);
        result.type()=op[0].type();
        return result;
      }
      else if(id=="bvlshr" || id=="bvashl" || id=="bvshl")
      {
        if(op.size()!=2)
        {
          error() << "bit shift must have two operands" << eom;
          return nil_exprt();
        }

        shl_exprt result(op[0], op[1]);
        result.type()=op[0].type();
        return result;
      }
      else if(id=="bvand")
      {
        bitand_exprt result;
        result.operands()=op;

        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();

        return result;
      }
      else if(id=="bvor")
      {
        bitor_exprt result;
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();
        return result;
      }
      else if(id=="bvxor")
      {
        bitxor_exprt result;
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();
        return result;
      }
      else if(id=="bvnot" || id=="bvneg")
      {
        bitnot_exprt result;
        result.operands()=op;
        result.type()=result.op0().type();
        return result;
      }
      else if(id=="bvadd" || id=="+")
      {
        plus_exprt result;
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();
        return result;
      }
      else if(id=="bvsub" || id=="-")
      {
        minus_exprt result;
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();
        return result;
      }
      else if(id=="bvmul" || id=="*")
      {
        mult_exprt result;
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();
        return result;
      }
      else if(id=="bvudiv")
      {
        div_exprt div_res;
        div_res.operands()=op;
        fix_binary_operation_operand_types(div_res);
        div_res.type()=div_res.op0().type();

        // is op1 equal to zero? If it is, division returns max value of op0
        equal_exprt op_divbyzero;
        op_divbyzero.op0() = div_res.op1();
        op_divbyzero.op1() = constant_exprt("0", div_res.op1().type());
        op_divbyzero.type() = bool_typet();

        bv_spect spec(div_res.op0().type());
        if_exprt result(
            op_divbyzero,
            constant_exprt(integer2string(spec.max_value()), div_res.op0().type()),
            div_res);

        result.type()=div_res.type();
        return result;
      }
      else if(id == "bvsdiv")
      {
        div_exprt div_res;
        div_res.operands() = op;
        fix_binary_operation_operand_types(div_res);
        div_res.type() = div_res.op0().type();

        div_res.op0() = cast_bv_to_signed(div_res.op0());
        div_res.op1() = cast_bv_to_signed(div_res.op1());
        exprt signed_res = cast_bv_to_unsigned(div_res);

        // is op1 equal to zero? If it is, division returns max value of op0
        equal_exprt op_divbyzero;
        op_divbyzero.op0() = signed_res.op1();
        op_divbyzero.op1() = constant_exprt("0", signed_res.op1().type());
        op_divbyzero.type() = bool_typet();

        bv_spect spec(signed_res.op0().type());
        if_exprt result(op_divbyzero,
            constant_exprt(integer2string(spec.max_value()),
                signed_res.op0().type()), signed_res);

        result.type() = signed_res.type();
        return result;
      }
      else if(id=="/" || id=="div")
      {
        div_exprt result;
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();
        return result;
      }
      else if(id=="bvsrem" || id=="bvurem" || id=="%")
      {
        mod_exprt result;
        result.operands()=op;
        fix_binary_operation_operand_types(result);
        result.type()=result.op0().type();

        if(id=="bvsrem")
        {
          result.op0()=cast_bv_to_signed(result.op0());
          result.op1()=cast_bv_to_signed(result.op1());
          return cast_bv_to_unsigned(result);
        }

        return result;
      }
      else if(id=="ite")
      {
        if_exprt result;
        result.operands()=op;
        fix_ite_operation_result_type(result);
        return result;
      }
      else if(id=="=>" || id=="implies")
      {
        implies_exprt result;
        result.operands()=op;
        return result;
      }
      else
      {
        if(function_map.count(id)!=0)
        {
          return function_application(id, op);
        }
        else if(local_variable_map.find(id)!=local_variable_map.end())
        {
          symbol_exprt result(id, local_variable_map[id]);
          return result;
        }
        else if(let_variable_map.find(id)!=let_variable_map.end())
        {
          symbol_exprt result(id, let_variable_map[id]);
          return result;
        }
        else if(variable_map.find(id)!=variable_map.end())
        {
          symbol_exprt result(id, variable_map[id]);
          return result;
        }
        else
        {
          error() << "use of undeclared symbol or function " << id << eom;
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

mathematical_function_typet sygus_parsert::function_signature()
{
  mathematical_function_typet result;

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

  result.codomain()=sort();

  return result;
}

void sygus_parsert::command(const std::string &c)
{
  if(c=="declare-var")
  {
    if(next_token()!=SYMBOL)
    {
      error() << "expected a symbol after declare-var" << eom;
      ignore_command();
      return;
    }

    irep_idt id=buffer;

    if(variable_map.find(id)!=variable_map.end())
    {
      error() << "variable declared twice" << eom;
      ignore_command();
      return;
    }

    variable_map[id]=sort();
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

    if(function_map.find(id)!=function_map.end())
    {
      error() << "function declared twice" << eom;
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
  else if(c=="set-logic")
  {
    if(next_token()!=SYMBOL)
    {
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
      error() << "expected a symbol after define-fun" << eom;
      ignore_command();
      return;
    }

    irep_idt id=buffer;

    if(function_map.find(id)!=function_map.end())
    {
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
      error() << "expected a symbol after declare-var" << eom;
      ignore_command();
      return;
    }

    irep_idt id=buffer;

    if(variable_map.find(id)!=variable_map.end())
    {
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

mathematical_function_typet sygus_parsert::inv_function_signature()
{
  mathematical_function_typet result;

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

  result.codomain()=bool_typet();

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
  expr.type() = f.type.codomain();
  expr.arguments().resize(f.type.domain().size());
  // get arguments
  for(std::size_t i = 0; i < f.type.domain().size(); i++)
  {
    std::string var_id = id2string(f.type.domain()[i].get_identifier())
        + suffix;

    if(variable_map.find(var_id) == variable_map.end())
      error() << "use of undeclared variable " << var_id << eom;
    symbol_exprt operand(var_id, f.type.domain()[i].type());
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
    error() << "NTDef must begin with '('" << eom;
    return;
  }

  if(peek()==OPEN)
    next_token(); // symbol might be in another set of parenthesis

  if(next_token()!=SYMBOL)
  {
    error() << "NTDef must have a symbol" << eom;
    return;
  }

  sort();

  GTerm_seq();

  if(next_token()!=CLOSE)
  {
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

      assert(f.type.domain().size()==
             app.arguments().size());

      replace_symbolt replace_symbol;

      std::map<irep_idt, exprt> parameter_map;
      for(std::size_t i=0; i<f.type.domain().size(); i++)
      {
        const irep_idt p_identifier=
          f.type.domain()[i].get_identifier();

        replace_symbol.insert(p_identifier, app.arguments()[i]);
      }

      exprt body=f.body;
      replace_symbol(body);
      expand_function_applications(body);
      expr=body;
    }
  }
}

typet sygus_parsert::sort()
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
      error() << "expected symbol after '(' in a sort" << eom;
      return nil_typet();
    }

    if(buffer=="BitVec")
    {
      // this has slightly different symtax compared to SMT-LIB2
      if(next_token()!=NUMERAL)
      {
        error() << "expected number after BitVec" << eom;
        return nil_typet();
      }

      auto width=std::stoll(buffer);

      if(next_token()!=CLOSE)
      {
        error() << "expected ')' after BitVec width" << eom;
        return nil_typet();
      }

      return unsignedbv_typet(width);
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

