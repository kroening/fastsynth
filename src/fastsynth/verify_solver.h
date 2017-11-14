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

  std::map<symbol_exprt, exprt> expressions;

  std::map<function_application_exprt, exprt::operandst>
    get_counterexample();

protected:
  static exprt instantiate(
    const exprt &,
    const function_application_exprt &);

  std::set<function_application_exprt> applications;
};

