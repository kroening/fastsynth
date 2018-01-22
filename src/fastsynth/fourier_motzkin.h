#include <set>

#include <solvers/prop/prop_conv.h>

class fourier_motzkint:public prop_conv_solvert
{
public:
  virtual literalt convert_rest(const exprt &) override;

  decision_proceduret::resultt dec_solve() override;

  std::set<exprt> existential_variables;

  fourier_motzkint(const namespacet &_ns, propt &_prop):
    prop_conv_solvert(_ns, _prop)
  {
  }

  std::string decision_procedure_text() const override
  {
    return "Fourier-Motzkin variable elimination";
  }

protected:
  struct constraintt
  {
    literalt l;
    exprt expr;
    constraintt(literalt _l, const exprt &_expr):
      l(_l), expr(_expr)
    {
    }
  };

  using constraintst=std::vector<constraintt>;
  constraintst constraints;

  void assignment();
};
