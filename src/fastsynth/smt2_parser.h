/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SMT2_SMT2_PARSER_H
#define CPROVER_SOLVERS_SMT2_SMT2_PARSER_H

#include <iosfwd>
#include <string>

class smt2_tokenizert
{
public:
  explicit smt2_tokenizert(std::istream &_in):
    in(_in), ok(true), peeked(false), token(NONE)
  {
  }

  operator bool()
  {
    return ok;
  }

protected:
  std::istream &in;
  std::string buffer;
  bool ok, peeked;
  using tokent=enum { NONE, END_OF_FILE, ERROR, STRING_LITERAL,
                      NUMERAL, SYMBOL, OPEN, CLOSE };
  tokent token;

  // parse errors
  virtual void error(const std::string &) = 0;

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

  void operator()()
  {
    command_sequence();
  }

protected:
  void command_sequence();

  virtual void command(const std::string &)
  {
    ignore_command();
  }

  void ignore_command();
};

#endif // CPROVER_SOLVERS_SMT2_SMT2_PARSER_H
