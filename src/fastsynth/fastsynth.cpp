#include <iostream>
#include <fstream>
#include <cstdlib>

#include <util/cmdline.h>
#include <util/cout_message.h>
#include <util/config.h>
#include <util/arith_tools.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/goto_convert_functions.h>

#include <goto-symex/goto_symex.h>
#include <goto-symex/symex_target_equation.h>

#include <ansi-c/ansi_c_language.h>

#include <langapi/mode.h>
#include <langapi/language_util.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

irep_idt ID_cegis;

class cegis_exprt:public multi_ary_exprt
{
public:
  explicit cegis_exprt(const typet &_type):
    multi_ary_exprt(ID_cegis, _type)
  {
  }
  
  void set_identifier(const irep_idt &_identifier)
  {
    set(ID_identifier, _identifier);
  }
  
  irep_idt get_identifier() const
  {
    return get(ID_identifier);
  }  
};

goto_modelt get_goto_model(
  const std::string &source,
  message_handlert &mh)
{
  messaget message(mh);
  std::ifstream in(source);
  
  if(!in)
  {
    std::cerr << "Failed to open `" << source << "'\n";
    exit(1);
  }
  
  ansi_c_languaget language;
  language.set_message_handler(mh);
  
  if(language.parse(in, source))
  {
    std::cerr << "Parsing error\n";
    exit(1);
  }

  goto_modelt goto_model;  
  
  if(language.typecheck(goto_model.symbol_table, ""))
  {
    std::cerr << "Conversion error\n";
    exit(1);
  }
  
  if(language.final(goto_model.symbol_table))
  {
    std::cerr << "Conversion error\n";
    exit(1);
  }
  
  goto_convert(goto_model, mh);

  return goto_model;
}

std::set<irep_idt> find_expressions(const goto_modelt &goto_model)
{
  std::set<irep_idt> result;

  for(auto &s : goto_model.symbol_table.symbols)
  {
    if(!s.second.is_state_var &&
       s.second.type.id()==ID_code &&
       s.second.value.is_nil() &&
       has_prefix(id2string(s.first), "EXPRESSION"))
      result.insert(s.first);
  }

  return result;
}

void instrument_expressions(
  const std::set<irep_idt> &expressions,
  goto_modelt &goto_model)
{
  for(auto &f : goto_model.goto_functions.function_map)
    for(auto &i : f.second.body.instructions)
    {
      if(i.is_function_call())
      {
        auto &c=to_code_function_call(i.code);
        if(c.function().id()==ID_symbol)
        {
          irep_idt identifier=to_symbol_expr(c.function()).get_identifier();
          if(expressions.find(identifier)!=expressions.end() &&
             c.lhs().is_not_nil())
          {
            i.type=ASSIGN;
            cegis_exprt e(c.lhs().type());
            e.operands()=c.arguments();
            e.set_identifier(identifier);
            i.code=code_assignt(c.lhs(), e);
          }
        }
      }
    }
}

class verify_solvert:public bv_pointerst
{
public:
  typedef bv_pointerst BASEt;

  verify_solvert(const namespacet &_ns, propt &_prop):
    bv_pointerst(_ns, _prop)
  {
  }
  
  std::string decision_procedure_text() const override
  {
    return "CEGIS verification with "+prop.solver_text();
  }
  
  bvt convert_bitvector(const exprt &) override;

  resultt dec_solve() override;
  
  std::map<cegis_exprt, exprt> expressions;
  
  typedef std::vector<exprt> argumentst;
  argumentst get_arguments(const cegis_exprt &) const;
};

bvt verify_solvert::convert_bitvector(const exprt &expr)
{
  if(expr.id()==ID_cegis)
  {
    const auto &e=static_cast<const cegis_exprt &>(expr);
    auto e_it=expressions.find(e);
    
    exprt result=e_it==expressions.end()?
      from_integer(0, e.type()):e_it->second;

    return BASEt::convert_bitvector(result);
  }
  else
    return BASEt::convert_bitvector(expr);
}

verify_solvert::argumentst verify_solvert::get_arguments(
  const cegis_exprt &e) const
{
  argumentst result;
  result.resize(e.operands().size(), nil_exprt());

  //for(const auto &p : 
  
  return result;
}

decision_proceduret::resultt verify_solvert::dec_solve()
{
  return BASEt::dec_solve();
}

class synth_solvert:public bv_pointerst
{
public:
  typedef bv_pointerst BASEt;

  synth_solvert(const namespacet &_ns, propt &_prop):
    bv_pointerst(_ns, _prop)
  {
  }
  
  std::string decision_procedure_text() const override
  {
    return "CEGIS synthesis with "+prop.solver_text();
  }
  
  bvt convert_bitvector(const exprt &) override;

  resultt dec_solve() override;
 
  struct e_datat
  {
    struct instructiont
    {
      explicit instructiont(unsigned _pc):pc(_pc)
      {
      }
      
      unsigned pc;
      
      struct optiont
      {
        exprt expr, sel;
      };

      std::vector<optiont> options;

      void add_option(const exprt &expr)
      {
        options.push_back(optiont());
        options.back().expr=expr;
      }
      
      symbol_exprt result_symbol;

      exprt result_constraint(const irep_idt &identifier)
      {
        std::size_t sel_count=0;
        
        for(auto &o : options)
        {
          irep_idt sel_id=id2string(identifier)+"_s"+
            std::to_string(pc)+"_"+std::to_string(sel_count);
          o.sel=symbol_exprt(sel_id, bool_typet());
        }
        
        // make the last one 'true'
        if(!options.empty())
          options.back().sel=true_exprt();

        exprt result_expr=nil_exprt();
        exprt selector=nil_exprt();

        for(const auto &o : options)        
        {
          if(result_expr.is_nil())
            result_expr=o.expr;
          else
            result_expr=if_exprt(selector, result_expr, o.expr);

          selector=o.sel;
          sel_count++;
        }

        result_symbol=symbol_exprt(
          id2string(identifier)+"_r"+std::to_string(pc),
          result_expr.type());

        return equal_exprt(result_symbol, result_expr);
      }
    };
  
    std::vector<instructiont> instructions;
  };
  
  std::map<cegis_exprt, e_datat> e_data_map;

  exprt get_expression(
    const cegis_exprt &,
    const e_datat &) const; 

  std::map<cegis_exprt, exprt> get_expressions() const;  
};

bvt synth_solvert::convert_bitvector(const exprt &expr)
{
  if(expr.id()==ID_cegis)
  {
    const auto &e=static_cast<const cegis_exprt &>(expr);
    const irep_idt identifier=e.get_identifier();
    
    e_datat &e_data=e_data_map[e];

    unsigned pc=0;
    
    e_data.instructions.push_back(e_datat::instructiont(pc));
    auto &instruction=e_data.instructions.back();
    
    irep_idt const_id=id2string(identifier)+"_c"+std::to_string(pc);
    symbol_exprt constant_value(const_id, expr.type());
    instruction.add_option(constant_value);

    for(const auto &arg : e.operands())
      if(arg.type()==e.type())
        instruction.add_option(arg);
      else
        instruction.add_option(typecast_exprt(arg, e.type()));

    exprt constraint=instruction.result_constraint(identifier);
    set_to_true(constraint);

    status() << "Constraint: " << from_expr(ns, "", constraint) << eom;

    assert(!e_data.instructions.empty());

    symbol_exprt final_result=
      e_data.instructions.back().result_symbol;
    
    return BASEt::convert_bitvector(final_result);
  }
  else
    return BASEt::convert_bitvector(expr);
}

std::map<cegis_exprt, exprt> synth_solvert::get_expressions() const
{
  std::map<cegis_exprt, exprt> result;

  for(const auto &e : e_data_map)
    result[e.first]=
      get_expression(e.first, e.second);

  return result;
}

exprt synth_solvert::get_expression(
  const cegis_exprt &e,
  const e_datat &e_data) const
{
  std::vector<exprt> results;
  results.resize(e_data.instructions.size(), nil_exprt());
  assert(!e_data.instructions.empty());

  for(unsigned pc=0; pc<e_data.instructions.size(); pc++)
  {
    const auto &instruction=e_data.instructions[pc];
    exprt &result=results[pc];

    for(const auto &o : instruction.options)
    {
      exprt sel_value=get(o.sel);
      if(sel_value.is_true())
      {
        result=get(o.expr);
        break;
      }
    }
    
    status() << from_expr(ns, "", instruction.result_symbol)
             << " := "
             << from_expr(ns, "", result)
             << eom;
  }

  return results.back();
}

decision_proceduret::resultt synth_solvert::dec_solve()
{
  return BASEt::dec_solve();
}

class cegist:public messaget
{
public:
  explicit cegist(const namespacet &_ns):ns(_ns)
  {
  }

  decision_proceduret::resultt operator()(
    symex_target_equationt &);
  
  std::map<cegis_exprt, exprt> expressions;

protected:
  const namespacet &ns;
  
  void convert_negation(
    symex_target_equationt &,
    prop_convt &);
};

decision_proceduret::resultt cegist::operator()(
  symex_target_equationt &equation)
{
  unsigned iteration=0;
  
  // now enter the CEGIS loop
  while(true)
  {
    iteration++;
    status() << "CEGIS iteration " << iteration << eom;
    
    for(const auto &e : expressions)
      debug() << e.first.get_identifier()
              << " -> " << from_expr(ns, "", e.second) << eom;

    status() << "Verification phase" << eom;

    satcheckt verify_satcheck;
    verify_solvert verify_solver(ns, verify_satcheck);
    verify_satcheck.set_message_handler(get_message_handler());
    verify_solver.set_message_handler(get_message_handler());
    verify_solver.expressions=expressions;

    equation.convert(verify_solver);

    switch(verify_solver())
    {
    case decision_proceduret::resultt::D_SATISFIABLE: // counterexample
      break;

    case decision_proceduret::resultt::D_UNSATISFIABLE: // done, got solution
      result() << "VERIFICATION SUCCESSFUL" << eom;
      return decision_proceduret::resultt::D_SATISFIABLE;

    case decision_proceduret::resultt::D_ERROR:
      return decision_proceduret::resultt::D_ERROR;
    }
    
    status() << "Synthesis phase" << eom;

    satcheckt synth_satcheck;
    synth_solvert synth_solver(ns, synth_satcheck);
    synth_satcheck.set_message_handler(get_message_handler());
    synth_solver.set_message_handler(get_message_handler());

    convert_negation(equation, synth_solver);

    switch(synth_solver())
    {
    case decision_proceduret::resultt::D_SATISFIABLE: // got candidate
      {
        std::map<cegis_exprt, exprt> old_expressions;
        old_expressions.swap(expressions);
        expressions=synth_solver.get_expressions();
        if(old_expressions==expressions)
        {
          error() << "NO PROGRESS MADE" << eom;
          return decision_proceduret::resultt::D_ERROR;
        }
      }
      break;

    case decision_proceduret::resultt::D_UNSATISFIABLE: // no candidate
      error() << "FAILED TO GET CANDIDATE" << eom;
      return decision_proceduret::resultt::D_UNSATISFIABLE;

    case decision_proceduret::resultt::D_ERROR:
      return decision_proceduret::resultt::D_ERROR;
    }
  }
}

void cegist::convert_negation(
  symex_target_equationt &equation,
  prop_convt &prop_conv)
{
  // all but assertions and assumptions
  equation.convert_guards(prop_conv);
  equation.convert_assignments(prop_conv);
  equation.convert_decls(prop_conv);
  equation.convert_goto_instructions(prop_conv);
  equation.convert_io(prop_conv);
  equation.convert_constraints(prop_conv);  
  
  // now do assertions and assumptions
  for(auto &step : equation.SSA_steps)
  {
    if(step.is_assert() ||
       step.is_assume())
    {
      prop_conv.set_to_true(step.cond_expr);
      step.cond_literal=const_literal(true);
    }
  }
}

int main(int argc, const char *argv[])
{
  ID_cegis="cegis";

  console_message_handlert mh;
  messaget message(mh);

  register_language(new_ansi_c_language);

  cmdlinet cmdline;
  if(cmdline.parse(argc, argv, ""))
  {
    std::cerr << "Usage error\n";
    return 1;
  }
  
  config.set(cmdline);
  config.ansi_c.set_arch_spec_i386();
  
  if(cmdline.args.size()!=1)
  {
    std::cerr << "Usage error\n";
    return 1;
  }
  
  goto_modelt goto_model=get_goto_model(cmdline.args[0], mh);
  
  auto expressions=find_expressions(goto_model);
  
  for(const auto &i : expressions)
    message.status() << "EXPRESSION: " << i << messaget::eom;

  instrument_expressions(expressions, goto_model);

  symbol_tablet new_symbol_table;
  namespacet ns(goto_model.symbol_table, new_symbol_table);
  symex_target_equationt equation(ns);
  goto_symext goto_symex(ns, new_symbol_table, equation);
  
  goto_symex(goto_model.goto_functions);

  #if 0
  equation.output(std::cout);
  return 0;
  #endif
  
  cegist cegis(ns);
  cegis.set_message_handler(mh);
  
  switch(cegis(equation))
  {
  case decision_proceduret::resultt::D_SATISFIABLE:
    for(const auto &e : cegis.expressions)
      message.result() << e.first << " -> "
                       << from_expr(ns, "", e.second) << messaget::eom;
    break;
    
  default:;
  }
}
