#include "synth_encoding.h"

void e_datat::setup(
  const function_application_exprt &e,
  const std::size_t program_size)
{
  if(setup_done) return;
  setup_done=true;

  function_symbol=e.function();
  const irep_idt &identifier=function_symbol.get_identifier();

  const auto &arguments=e.arguments();
  parameter_types.resize(arguments.size());
  for(std::size_t i=0; i<parameter_types.size(); i++)
    parameter_types[i]=arguments[i].type();

  instructions.reserve(program_size);

  for(std::size_t pc=0; pc<program_size; pc++)
  {
    instructions.push_back(instructiont(pc));
    auto &instruction=instructions[pc];

    // constant
    irep_idt const_val_id=id2string(identifier)+"_"+std::to_string(pc)+"_cval";
    instruction.constant_val=symbol_exprt(const_val_id, e.type());

    // one of the arguments
    instruction.parameter_sel.resize(arguments.size());

    for(std::size_t i=0; i<arguments.size(); i++)
    {
      irep_idt param_sel_id=id2string(identifier)+"_"+
               std::to_string(pc)+"_p"+std::to_string(i)+"sel";
      instruction.parameter_sel[i]=symbol_exprt(param_sel_id, bool_typet());
    }

    // a binary operation

    static const irep_idt ops[]=
      { ID_plus, ID_minus, ID_shl };

    for(const auto &operation : ops)
      for(std::size_t operand0=0; operand0<pc; operand0++)
        for(std::size_t operand1=0; operand1<pc; operand1++)
        {
          std::size_t index=instruction.binary_ops.size();
          auto &binary_op=instruction.add_binary_op();

          irep_idt sel_id=id2string(identifier)+"_"+
                   std::to_string(pc)+"_b"+std::to_string(index)+"sel";
          binary_op.sel=symbol_exprt(sel_id, bool_typet());

          binary_op.operand0=operand0;
          binary_op.operand1=operand1;
          binary_op.operation=operation;
        }
  }
}

exprt e_datat::instructiont::result(
  const std::vector<exprt> &arguments,
  const std::vector<exprt> &results)
{
  // constant, which is last resort
  exprt result_expr=constant_val;

  // a parameter
  assert(arguments.size()==parameter_sel.size());

  for(std::size_t i=0; i<parameter_sel.size(); i++)
  {
    exprt selector=parameter_sel[i];
    result_expr=if_exprt(selector, arguments[i], result_expr);
  }

  // a binary operation
  for(const auto &binary_op : binary_ops)
  {
    exprt selector=binary_op.sel;

    assert(binary_op.operand0<results.size());
    assert(binary_op.operand1<results.size());

    binary_exprt binary_expr(binary_op.operation);
    binary_expr.op0()=results[binary_op.operand0];
    binary_expr.op1()=results[binary_op.operand1];

    // need to do some kind of promotion
    binary_expr.type()=binary_expr.op0().type();

    result_expr=if_exprt(selector, binary_expr, result_expr);
  }

  return result_expr;
}

exprt e_datat::result(
  const std::vector<exprt> &arguments)
{
  std::vector<exprt> results;
  results.resize(instructions.size(), nil_exprt());

  for(std::size_t pc=0; pc<instructions.size(); pc++)
    results[pc]=instructions[pc].result(arguments, results);

  assert(!results.empty());

  return results.back();
}

exprt e_datat::get_expression(
  const decision_proceduret &solver) const
{
  // this goes backwards,
  // i.e., outside-in from the synthesis case split

  assert(!instructions.empty());

  std::vector<exprt> results;
  results.resize(instructions.size(), nil_exprt());

  for(std::size_t pc=0; pc<instructions.size(); pc++)
  {
    const auto &instruction=instructions[pc];
    exprt &result=results[pc];
    result=nil_exprt();

    // a binary operation?
    // Need to go backwards

    for(auto b_op_it=instruction.binary_ops.rbegin();
        b_op_it!=instruction.binary_ops.rend();
        b_op_it++)
    {
      const auto &binary_op=*b_op_it;

      if(solver.get(binary_op.sel).is_true())
      {
        assert(binary_op.operand0<results.size());
        assert(binary_op.operand1<results.size());

        result=binary_exprt(
          results[binary_op.operand0],
          binary_op.operation,
          results[binary_op.operand1],
          results[binary_op.operand0].type());

        break;
      }
    }

    // a parameter?

    if(result.is_nil())
    {
      for(std::size_t i=0; i<instruction.parameter_sel.size(); i++)
      {
        std::size_t index=instruction.parameter_sel.size()-i-1;

        if(solver.get(instruction.parameter_sel[index]).is_true())
        {
          irep_idt p_identifier="synth::parameter"+std::to_string(index);
          result=symbol_exprt(p_identifier, parameter_types[index]);
          break;
        }
      }
    }

    if(result.is_nil())
    {
      // constant, this is the last resort
      result=solver.get(instruction.constant_val);
    }
  }

  return results.back();
}

exprt synth_encodingt::operator()(const exprt &expr)
{
  if(expr.id()==ID_function_application)
  {
    auto tmp=to_function_application_expr(expr);

    // apply recursively to arguments
    for(auto &op : tmp.arguments())
      op=(*this)(op);

    e_datat &e_data=e_data_map[tmp.function()];
    exprt final_result=e_data(tmp, program_size);

    return final_result;
  }
  else if(expr.id()==ID_symbol)
  {
    // add the suffix
    symbol_exprt tmp=to_symbol_expr(expr);
    tmp.set_identifier(id2string(tmp.get_identifier())+suffix);
    return tmp;
  }
  else
  {
    exprt tmp=expr;

    for(auto &op : tmp.operands())
      op=(*this)(op); // recursive call

    return tmp;
  }
}

exprt synth_encodingt::get_expression(
  const symbol_exprt &function_symbol,
  const decision_proceduret &solver) const
{
  const auto it=e_data_map.find(function_symbol);
  if(it==e_data_map.end()) return nil_exprt();
  return it->second.get_expression(solver);
}

std::map<symbol_exprt, exprt> synth_encodingt::get_expressions(
  const decision_proceduret &solver) const
{
  std::map<symbol_exprt, exprt> result;

  for(const auto &it : e_data_map)
  {
    result[it.first]=it.second.get_expression(solver);
  }

  return result;
}

