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
      explicit instructiont(std::size_t _pc):pc(_pc)
      {
      }
      
      std::size_t pc;
      
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

      // constraint on the result of the function application
      exprt result_constraint(const irep_idt &identifier);
    };
  
    std::vector<instructiont> instructions;
  };
  
  std::map<function_application_exprt, e_datat> e_data_map;

  exprt get_expression(
    const function_application_exprt &,
    const e_datat &) const; 

  std::map<function_application_exprt, exprt> get_expressions() const;  
};

