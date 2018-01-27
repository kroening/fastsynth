#ifndef CPROVER_FASTSYNTH_CEGIS_H_
#define CPROVER_FASTSYNTH_CEGIS_H_

#include <util/decision_procedure.h>

#include "cegis_types.h"

class synth_encodingt;
class verify_encodingt;
class prop_convt;
class learnt;

class cegist:public messaget
{
public:
  // constructor
  explicit cegist(const namespacet &_ns):
    max_program_size(0),
    incremental_solving(false),
    use_simp_solver(false),
    use_fm(false),
    ns(_ns)
  {
  }

  solutiont solution;

  decision_proceduret::resultt operator()(const problemt &);

  std::size_t max_program_size;
  bool incremental_solving;
  bool use_simp_solver;
  bool use_fm;

protected:
  const namespacet &ns;

  decision_proceduret::resultt loop(const problemt &, learnt &);
};

void output_expressions(
  const std::map<symbol_exprt, exprt> &,
  const namespacet &,
  std::ostream &);

#endif /* CPROVER_FASTSYNTH_CEGIS_H_ */
