#ifndef CPROVER_FASTSYNTH_VERIFY_H_
#define CPROVER_FASTSYNTH_VERIFY_H_

#include "cegis.h"
#include "verify_encoding.h"

/// Interface for classes that verify candidate solutions
class verifyt:public messaget
{
public:
  explicit verifyt(
    const namespacet &_ns,
    const cegist::problemt &_problem,
    message_handlert &_message_handler):
    messaget(_message_handler),
    ns(_ns), problem(_problem)
  {
  }

  /// Check a new candidate.
  /// \return \see decision_proceduret::resultt
  decision_proceduret::resultt operator()(
    const std::map<symbol_exprt, exprt> &);
    
  using counterexamplet=std::map<exprt, exprt>;

  const counterexamplet &get_counterexample() const
  {
    return counterexample;
  }
    
protected:
  const namespacet &ns;
  const cegist::problemt &problem;
  counterexamplet counterexample;

  void add_problem(verify_encodingt &, prop_convt &);
};

#endif /* CPROVER_FASTSYNTH_VERIFY_H_ */
