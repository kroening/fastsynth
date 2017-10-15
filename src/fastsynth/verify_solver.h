#include <solvers/flattening/bv_pointers.h>

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
  
  std::map<function_application_exprt, exprt> expressions;
  
  typedef std::vector<exprt> argumentst;
  argumentst get_arguments(const function_application_exprt &) const;
};

