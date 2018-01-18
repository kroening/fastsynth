#ifndef CPROVER_FASTSYNTH_VERIFY_ENCODING_H_
#define CPROVER_FASTSYNTH_VERIFY_ENCODING_H_

#include <set>

#include <util/std_expr.h>
#include <util/decision_procedure.h>

class verify_encodingt
{
public:
  exprt operator()(const exprt &) const;

  std::map<symbol_exprt, exprt> expressions;
  std::set<exprt> free_variables;

  using counterexamplet=std::map<exprt, exprt>;

  counterexamplet get_counterexample(
    const decision_proceduret &) const;

protected:
  exprt instantiate(
    const exprt &expr,
    const function_application_exprt &e) const;
};

#endif /* CPROVER_FASTSYNTH_VERIFY_ENCODING_H_ */
