#include <solvers/flattening/bv_pointers.h>

class verify_encodingt
{
public:
  exprt operator()(const exprt &);

  std::map<symbol_exprt, exprt> expressions;

  std::map<function_application_exprt, exprt::operandst>
    get_counterexample(const decision_proceduret &);

protected:
  std::set<function_application_exprt> applications;

  exprt instantiate(
    const exprt &expr,
    const function_application_exprt &e);
};

