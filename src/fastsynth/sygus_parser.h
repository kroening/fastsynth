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

  std::list<exprt> constraints;
  std::string logic, action;

  using variable_mapt=std::map<irep_idt, typet>;
  variable_mapt variable_map;

  virtual void error(const std::string &s) override;

  exprt expression();
  typet sort();
  exprt::operandst operands();
};

