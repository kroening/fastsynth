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

  virtual void command(const std::string &) override;

  exprt::operandst constraints;
  std::string logic, action;

  std::set<irep_idt> synth_fun_set;

  virtual void error(const std::string &s) override;

  void expand_function_applications(exprt &);

protected:
  void NTDef_seq();
  void GTerm_seq();
  void NTDef();
  void GTerm();
};

