#ifndef CPROVER_FASTSYNTH_CEGIS_H_
#define CPROVER_FASTSYNTH_CEGIS_H_

#include <solvers/decision_procedure.h>

#include <util/message.h>

#include "cegis_types.h"

class synth_encoding_baset;
class verify_encoding_baset;
class prop_convt;
class learnt;
class verifyt;

class cegist:public messaget
{
public:
  // constructor
  explicit cegist(const namespacet &_ns):
    min_program_size(1),
    max_program_size(0),
    max_iterations(0),
    incremental_solving(false),
    use_simp_solver(false),
    use_fm(false),
    enable_bitwise(false),
    use_smt(false),
    logic("BV"),
    ns(_ns)
  {
  }

  solutiont solution;

  decision_proceduret::resultt operator()(
      const problemt &, synth_encoding_baset &synth_encoding,
      verify_encoding_baset &verify_encoding);

  std::size_t min_program_size;
  std::size_t max_program_size;
  std::size_t max_iterations;
  bool incremental_solving;
  bool use_simp_solver;
  bool use_fm;
  bool enable_bitwise;
  bool enable_division;
  bool use_smt;
  std::string logic; // used by smt

protected:
  const namespacet &ns;

  decision_proceduret::resultt loop(
    const problemt &,
    learnt &,
    verifyt &);
};

void output_expressions(
  const std::map<symbol_exprt, exprt> &,
  const namespacet &,
  std::ostream &);

#endif /* CPROVER_FASTSYNTH_CEGIS_H_ */
