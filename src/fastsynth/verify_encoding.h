#ifndef CPROVER_FASTSYNTH_VERIFY_ENCODING_H_
#define CPROVER_FASTSYNTH_VERIFY_ENCODING_H_

#include <set>

#include <util/std_expr.h>
#include <util/decision_procedure.h>

#include "cegis_types.h"

class verify_encodingt
{
public:
  exprt operator()(const exprt &);

  std::map<symbol_exprt, exprt> functions;
  std::set<exprt> free_variables;

  std::map<function_application_exprt, exprt> f_apps;

  counterexamplet get_counterexample(
    const decision_proceduret &) const;

protected:
  exprt instantiate(
    const exprt &expr,
    const function_application_exprt &e) const;
};

#endif /* CPROVER_FASTSYNTH_VERIFY_ENCODING_H_ */
