#ifndef CPROVER_FASTSYNTH_FM_VERIFY_H_
#define CPROVER_FASTSYNTH_FM_VERIFY_H_

#include "verify.h"

/// verify a candidate solution with FM generalization
class fm_verifyt:public verifyt
{
public:
  fm_verifyt(
    const namespacet &_ns,
    const problemt &_problem,
    message_handlert &_message_handler):
    verifyt(_ns, _problem, _message_handler)
  {
  }

  /// Check a new candidate.
  /// \return \see decision_proceduret::resultt
  virtual decision_proceduret::resultt operator()(solutiont &);
};

#endif /* CPROVER_FASTSYNTH_VERIFY_H_ */
