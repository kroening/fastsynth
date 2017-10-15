#include <solvers/flattening/bv_pointers.h>

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
  
  std::map<function_application_exprt, e_datat> e_data_map;

  exprt get_expression(
    const function_application_exprt &,
    const e_datat &) const; 

  std::map<function_application_exprt, exprt> get_expressions() const;  
};

