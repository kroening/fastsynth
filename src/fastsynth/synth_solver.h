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

  std::map<symbol_exprt, exprt> get_expressions() const;

  std::string suffix;

protected:
  struct e_datat
  {
  public:
    e_datat():setup_done(false) { }

    struct instructiont
    {
      explicit instructiont(std::size_t _pc):pc(_pc)
      {
      }

      std::size_t pc;

      // constant
      symbol_exprt constant_sel;
      symbol_exprt constant_val;

      // parameter
      std::vector<symbol_exprt> parameter_sel;
      
      // result of the instruction
      // for a set of arguments
      exprt result(const std::vector<exprt> &arguments);
    };
  
    std::vector<instructiont> instructions;

    // result of the function application
    // for a set of arguments
    exprt result(const std::vector<exprt> &arguments);

    void setup(const function_application_exprt &);
    std::vector<typet> parameter_types;
    symbol_exprt function_symbol;

  protected:
    bool setup_done;
  };

  std::map<symbol_exprt, e_datat> e_data_map;
  exprt get_expression(const e_datat &) const;
};

