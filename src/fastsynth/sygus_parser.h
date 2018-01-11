#include "smt2_parser.h"

#include <util/expr.h>

#include "function.h"

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

  using variable_mapt=std::map<irep_idt, typet>;
  variable_mapt variable_map;

  struct functiont
  {
    function_typet type;
    exprt body;
  };

  using function_mapt=std::map<irep_idt, functiont>;
  function_mapt function_map;

  virtual void error(const std::string &s) override;

  void NTDef_seq();
  void GTerm_seq();
  void NTDef();
  void GTerm();
};

