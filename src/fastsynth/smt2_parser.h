/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SMT2_SMT2_PARSER_H
#define CPROVER_SOLVERS_SMT2_SMT2_PARSER_H

#include <util/parser.h>

#include <string>
#include <util/std_expr.h>

#include "function.h"

class function_typet;

class smt2_tokenizert:public parsert
{
public:
  explicit smt2_tokenizert(std::istream &_in):
    ok(true), peeked(false), token(NONE)
  {
    in=&_in;
  }

  operator bool()
  {
    return ok;
  }

protected:
  std::string buffer;
  bool ok, peeked;
  using tokent=enum { NONE, END_OF_FILE, ERROR, STRING_LITERAL,
                      NUMERAL, SYMBOL, OPEN, CLOSE };
  tokent token;

  tokent next_token();

  tokent peek()
  {
    if(peeked)
      return token;
    else
    {
      next_token();
      peeked=true;
      return token;
    }
  }

private:
  tokent get_decimal_numeral();
  tokent get_hex_numeral();
  tokent get_bin_numeral();
  tokent get_simple_symbol();
  tokent get_quoted_symbol();
  tokent get_string_literal();
  static bool is_simple_symbol_character(char);
};

class new_smt2_parsert:public smt2_tokenizert
{
public:
  explicit new_smt2_parsert(std::istream &_in):smt2_tokenizert(_in)
  {
  }

  virtual bool parse() override
  {
    command_sequence();
    return !ok;
  }

  struct functiont
  {
    function_typet type;
    exprt body;
  };

  using function_mapt=std::map<irep_idt, functiont>;
  function_mapt function_map;

  using variable_mapt=std::map<irep_idt, typet>;
  variable_mapt variable_map;
  variable_mapt local_variable_map;

protected:
  void command_sequence();

  virtual void command(const std::string &);

  void ignore_command();
  void declare_var();
  void define_fun();

  exprt expression();
  let_exprt let_expression(bool first_in_chain);
  typet sort();
  exprt::operandst operands();
  function_typet function_signature();
  exprt function_application(const irep_idt &identifier, const exprt::operandst &op);
  void fix_binary_operation_operand_types(exprt &expr);
  void fix_ite_operation_result_type(if_exprt &expr);
  exprt cast_bv_to_signed(exprt &expr);
  exprt cast_bv_to_unsigned(exprt &expr);
  void check_bitvector_operands(exprt &expr);
};

#endif // CPROVER_SOLVERS_SMT2_SMT2_PARSER_H
