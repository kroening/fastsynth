#ifndef CPROVER_FASTSYNTH_VERIFY_H_
#define CPROVER_FASTSYNTH_VERIFY_H_

#include "cegis_types.h"
#include "verify_encoding.h"

#include <util/message.h>

class decision_proceduret;

/// verify a candidate solution
class verifyt:public messaget
{
public:
  verifyt(
    const namespacet &_ns,
    const problemt &_problem,
    message_handlert &_message_handler):
    messaget(_message_handler),
    use_smt(false),
    ns(_ns), problem(_problem)
  {
  }

  /// Check a new candidate.
  /// \return \see decision_proceduret::resultt
  virtual decision_proceduret::resultt operator()(const solutiont &);
    
  const counterexamplet &get_counterexample() const
  {
    return counterexample;
  }

  bool use_smt;
  std::string logic;

protected:
  const namespacet &ns;
  const problemt &problem;
  counterexamplet counterexample;

  void add_problem(verify_encodingt &, decision_proceduret &);

  void output(
    const solutiont::functionst &,
    std::ostream &);
};

#endif /* CPROVER_FASTSYNTH_VERIFY_H_ */
