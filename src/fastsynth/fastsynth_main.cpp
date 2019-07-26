/*******************************************************************\

 Module: Fastsynth Main Module

 Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "c_frontend.h"
#include "smt2_frontend.h"
#include "statement_list_frontend.h"
#include "sygus_frontend.h"

#include <util/cmdline.h>
#include <util/suffix.h>

#include <iostream>

#define FASTSYNTH_OPTIONS                                                      \
  "(min-program-size):"                                                        \
  "(max-program-size):"                                                        \
  "(incremental)"                                                              \
  "(simplifying-solver)"                                                       \
  "(fm)"                                                                       \
  "(local-search)"                                                            \
  "(no-bitwise)"                                                               \
  "(verbosity):"                                                               \
  "(smt)"                                                                      \
  "(literals)"                                                                 \
  "(enable-division)"

/// File ending of Siemens STL source files. Used to determine the language
/// frontend that shall be used.
#define STATEMENT_LIST_FILE_ENDING ".awl"

/// File ending of SMT2 files. Used to determine the language frontend that
/// shall be used.
#define SMT2_FILE_ENDING ".smt2"

/// File ending of Sygus files. Used to determine the language frontend that
/// shall be used.
#define SYGUS_FILE_ENDING ".sl"

int main(int argc, const char *argv[])
{
  cmdlinet cmdline;
  if(cmdline.parse(argc, argv, FASTSYNTH_OPTIONS))
  {
    std::cerr << "Usage error\n";
    return 1;
  }

  if(cmdline.args.size() != 1)
  {
    std::cerr << "Usage error\n";
    return 1;
  }

  try
  {
    if(has_suffix(cmdline.args.back(), SYGUS_FILE_ENDING))
      return sygus_frontend(cmdline);
    else if(has_suffix(cmdline.args.back(), SMT2_FILE_ENDING))
      return smt2_frontend(cmdline);
    else if(has_suffix(cmdline.args.back(), STATEMENT_LIST_FILE_ENDING))
      return statement_list_frontend(cmdline);
    else
      return c_frontend(cmdline);
  }
  catch(const char *s)
  {
    std::cerr << "Error: " << s << '\n';
  }
  catch(const std::string &s)
  {
    std::cerr << "Error: " << s << '\n';
  }
}
