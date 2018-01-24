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
  void eliminate();
  static exprt negate(const exprt &);

  struct addendt
  {
    bool negative;
    exprt expr;
    void negate() { negative=!negative; }
    addendt():negative(false) { }
  };

  friend bool operator<(const addendt &a, const addendt &b)
  {
    if(a.expr<b.expr) return true;
    return a.negative < b.negative;
  }

  using addendst=std::vector<addendt>;

  static void negate(addendst &addends)
  {
    for(auto &a : addends)
      a.negate();
  }

  class rowt
  {
  public:
    addendst addends;
    bool is_strict;
    void negate();
    explicit rowt(const exprt &);
    operator bool() const { return failed; }
    mp_integer bound;

    std::vector<addendt>::const_iterator find(const exprt &src) const;
    std::vector<addendt>::const_iterator end() const { return addends.end(); }
    void eliminate_strict();
    bool is_inconsistent() const;
    bool is_tautology() const { return addends.empty() && !is_inconsistent(); }
    bool is_empty() const { return addends.empty(); }
    void normalize();

  protected:
    bool failed;
    void collect_addends(const exprt &, bool negate);
  };

  std::string as_string(const std::vector<addendt> &) const;
  std::string as_string(const rowt &) const;

  void subsumption(std::list<rowt> &);
};
