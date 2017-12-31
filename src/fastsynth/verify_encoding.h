#include <set>

#include <util/std_expr.h>
#include <util/decision_procedure.h>

class verify_encodingt
{
public:
  exprt operator()(const exprt &);

  std::map<symbol_exprt, exprt> expressions;

  using counterexamplet=std::map<exprt, exprt>;

  counterexamplet get_counterexample(const decision_proceduret &);

protected:
  std::set<exprt> free_variables;

  exprt instantiate(
    const exprt &expr,
    const function_application_exprt &e);
};

