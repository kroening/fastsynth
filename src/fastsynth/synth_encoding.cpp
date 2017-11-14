#include "synth_encoding.h"

exprt e_datat::instructiont::result(
  const std::vector<exprt> &arguments)
{
  if(parameter_sel.empty())
    return constant_val;

  exprt result_expr=constant_val;
  exprt selector=constant_sel;

  assert(arguments.size()==parameter_sel.size());

  for(std::size_t i=0; i<parameter_sel.size(); i++)
  {
    result_expr=if_exprt(selector, result_expr, arguments[i]);
    selector=parameter_sel[i];
  }

  return result_expr;
}

void e_datat::setup(
  const function_application_exprt &e)
{
  if(setup_done) return;
  setup_done=true;

  function_symbol=e.function();
  const irep_idt &identifier=function_symbol.get_identifier();

  instructions.reserve(1);

  for(std::size_t pc=0; pc<1; pc++)
  {
    instructions.push_back(instructiont(pc));
    auto &instruction=instructions[pc];

    // constant
    irep_idt const_sel_id=id2string(identifier)+"_"+std::to_string(pc)+"_csel";
    irep_idt const_val_id=id2string(identifier)+"_"+std::to_string(pc)+"_cval";
    instruction.constant_sel=symbol_exprt(const_sel_id, bool_typet());
    instruction.constant_val=symbol_exprt(const_val_id, e.type());

    // one of the arguments
    const auto &arguments=e.arguments();
    instruction.parameter_sel.resize(arguments.size());

    for(std::size_t i=0; i<arguments.size(); i++)
    {
      irep_idt param_sel_id=id2string(identifier)+"_"+
               std::to_string(pc)+"_p"+std::to_string(i)+"sel";
      instruction.parameter_sel[i]=symbol_exprt(param_sel_id, bool_typet());
    }
  }
}

exprt e_datat::result(
  const std::vector<exprt> &arguments)
{
  std::vector<exprt> results;
  results.resize(instructions.size());

  for(std::size_t pc=0; pc<instructions.size(); pc++)
    results[pc]=instructions[pc].result(arguments);

  assert(!results.empty());

  return results.back();
}

