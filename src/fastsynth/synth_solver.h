#include <solvers/flattening/bv_pointers.h>

#include "synth_encoding.h"

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
  std::map<symbol_exprt, e_datat> e_data_map;
  exprt get_expression(const e_datat &) const;
};

