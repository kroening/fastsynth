#include <set>

#include "smt2_parser.h"

#include <util/expr.h>

class sygus_parsert:public new_smt2_parsert
{
public:
  explicit sygus_parsert(std::istream &_in):
    new_smt2_parsert(_in)
  {
  }

  enum invariant_variablet {PRIMED, UNPRIMED};
  enum invariant_constraint_functiont {PRE, INV, TRANS, POST};

  virtual void command(const std::string &) override;

  exprt::operandst constraints;
  std::string logic, action;

  std::set<irep_idt> synth_fun_set;

  function_typet inv_function_signature();
  void expand_function_applications(exprt &);
  void generate_invariant_constraints();
  void apply_function_to_variables(
      function_application_exprt &expr,
      invariant_constraint_functiont id,
      invariant_variablet variable_use);


protected:
  void NTDef_seq();
  void GTerm_seq();
  void NTDef();
  void GTerm();
};

