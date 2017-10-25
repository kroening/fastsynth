#include <util/std_expr.h>
#include <util/decision_procedure.h>

class symex_target_equationt;
class prop_convt;

class cegist:public messaget
{
public:
  explicit cegist(const namespacet &_ns):ns(_ns)
  {
  }

  decision_proceduret::resultt operator()(
    symex_target_equationt &);
  
  std::map<symbol_exprt, exprt> expressions;

protected:
  const namespacet &ns;
  
  struct counterexamplet
  {
    // map function applications to values
    std::map<function_application_exprt, exprt> values;
  };

  using counterexamplest=std::vector<counterexamplet>;
  counterexamplest counterexamples;

  void convert_negation(
    symex_target_equationt &,
    prop_convt &);
};

