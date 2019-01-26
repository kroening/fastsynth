#ifndef CPROVER_FASTSYNTH_VERIFY_ENCODING_H_
#define CPROVER_FASTSYNTH_VERIFY_ENCODING_H_

#include <set>

#include <util/decision_procedure.h>
#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>

#include "cegis_types.h"

class verify_encodingt
{
public:
  exprt operator()(const exprt &) const;

  using functionst = solutiont::functionst;
  functionst functions;
  std::set<exprt> free_variables;

  counterexamplet get_counterexample(
    const decision_proceduret &) const;

  // check that the function body uses symbols that
  // are consistent with the signature of the function
  static void check_function_body(
    const mathematical_function_typet &signature,
    const exprt &body);

  static void check_function_bodies(const functionst &);

protected:
  exprt instantiate(
    const exprt &expr,
    const function_application_exprt &e) const;
};

#endif /* CPROVER_FASTSYNTH_VERIFY_ENCODING_H_ */
