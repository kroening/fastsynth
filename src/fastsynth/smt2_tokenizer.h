/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SMT2_SMT2_TOKENIZER_H
#define CPROVER_SOLVERS_SMT2_SMT2_TOKENIZER_H

#include <util/parser.h>

#include <string>

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

#endif // CPROVER_SOLVERS_SMT2_SMT2_PARSER_H
