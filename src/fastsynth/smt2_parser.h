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
  void tc_multi_ary(exprt &);
  void tc_binary_predicate(exprt &);
  void tc_binary(exprt &);

  let_exprt let_expression(bool first_in_chain);
  exprt function_application(const irep_idt &identifier, const exprt::operandst &op);
  void fix_binary_operation_operand_types(exprt &expr);
  void fix_ite_operation_result_type(if_exprt &expr);
  exprt cast_bv_to_signed(exprt &expr);
  exprt cast_bv_to_unsigned(exprt &expr);
  void check_bitvector_operands(exprt &expr);
};

#endif // CPROVER_SOLVERS_SMT2_SMT2_PARSER_H
