/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SMT2_SMT2_PARSER_H
#define CPROVER_SOLVERS_SMT2_SMT2_PARSER_H

#include <stack>

#include <util/std_expr.h>

#include "smt2_tokenizer.h"

class new_smt2_parsert:public smt2_tokenizert
{
public:
  explicit new_smt2_parsert(std::istream &_in):smt2_tokenizert(_in)
  {
    id_stack.push_back(id_mapt());
  }

  virtual bool parse() override
  {
    command_sequence();
    return !ok;
  }

  struct idt
  {
    typet type;
    exprt definition;
  };

  using id_mapt=std::map<irep_idt, idt>;
  std::vector<id_mapt> id_stack;

protected:
  void command_sequence();

  virtual void command(const std::string &);

  void ignore_command();
  exprt expression();
  typet sort();
  exprt::operandst operands();
  typet function_signature_declaration();
  typet function_signature_definition();
  exprt multi_ary(irep_idt, exprt::operandst &);
  exprt binary_predicate(irep_idt, exprt::operandst &);
  exprt binary(irep_idt, exprt::operandst &);

  let_exprt let_expression(bool first_in_chain);
  exprt function_application(const irep_idt &identifier, const exprt::operandst &op);
  exprt cast_bv_to_signed(const exprt &);
  exprt cast_bv_to_unsigned(const exprt &);
};

#endif // CPROVER_SOLVERS_SMT2_SMT2_PARSER_H
