#ifndef CPROVER_FASTSYNTH_VERIFY_H_
#define CPROVER_FASTSYNTH_VERIFY_H_

#include "cegis_types.h"
#include "verify_encoding.h"

#include <util/message.h>

class decision_proceduret;

/// verify a candidate solution
class verifyt:public messaget
{
  /// Encoding for the verification decision procedure call.
  verify_encoding_baset &verify_encoding;

public:
  verifyt(
    const namespacet &_ns,
    const problemt &_problem,
    verify_encoding_baset &verify_encoding,
    message_handlert &_message_handler):
    messaget(_message_handler),
    verify_encoding(verify_encoding),
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

  void add_problem(verify_encoding_baset &, decision_proceduret &);

  void output(
    const solutiont::functionst &,
    std::ostream &);
};

#endif /* CPROVER_FASTSYNTH_VERIFY_H_ */
