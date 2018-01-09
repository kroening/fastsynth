#include <util/std_expr.h>
#include <util/decision_procedure.h>

class synth_encodingt;
class verify_encodingt;
class prop_convt;

class cegist:public messaget
{
public:
  explicit cegist(const namespacet &_ns):
    max_program_size(0),
    incremental_solving(false),
    ns(_ns)
  {
  }

  class problemt
  {
  public:
    exprt::operandst side_conditions, constraints;
  };

  decision_proceduret::resultt operator()(const problemt &);
  
  std::map<symbol_exprt, exprt> expressions;

  std::size_t max_program_size;
  bool incremental_solving;

protected:
  const namespacet &ns;

  decision_proceduret::resultt incremental_loop(
    const problemt &);

  decision_proceduret::resultt non_incremental_loop(
    const problemt &);

  // map symbols to values
  using counterexamplet=std::map<exprt, exprt>;

  using counterexamplest=std::vector<counterexamplet>;

  counterexamplest counterexamples;

  void add_problem(
    const problemt &,
    verify_encodingt &,
    prop_convt &);

  void add_problem(
    const problemt &,
    synth_encodingt &,
    prop_convt &);

  void add_counterexample(
    const counterexamplet &,
    synth_encodingt &,
    prop_convt &);
};

void output_expressions(
  const std::map<symbol_exprt, exprt> &,
  const namespacet &,
  std::ostream &);
