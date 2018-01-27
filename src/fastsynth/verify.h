#ifndef CPROVER_FASTSYNTH_VERIFY_H_
#define CPROVER_FASTSYNTH_VERIFY_H_

#include "cegis_types.h"
#include "verify_encoding.h"

class prop_convt;

/// verify a candidate solution
class verifyt:public messaget
{
public:
  verifyt(
    const namespacet &_ns,
    const problemt &_problem,
    message_handlert &_message_handler):
    messaget(_message_handler),
    ns(_ns), problem(_problem)
  {
  }

  /// Check a new candidate.
  /// \return \see decision_proceduret::resultt
  virtual decision_proceduret::resultt operator()(solutiont &);
    
  const counterexamplet &get_counterexample() const
  {
    return counterexample;
  }

protected:
  const namespacet &ns;
  const problemt &problem;
  counterexamplet counterexample;

  void add_problem(verify_encodingt &, prop_convt &);

  void output(
    const solutiont::functionst &,
    std::ostream &);
};

#endif /* CPROVER_FASTSYNTH_VERIFY_H_ */
