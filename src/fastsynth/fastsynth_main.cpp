#include <iostream>

#include <util/suffix.h>
#include <util/cmdline.h>

#include "c_frontend.h"
#include "sygus_frontend.h"
#include "smt2_frontend.h"
#include "program_generator.h"

#define FASTSYNTH_OPTIONS \
   "(max-program-size):" \
   "(incremental)" \
   "(simplifying-solver)" \
   "(fm)" \
   "(no-bitwise)" \
   "(verbosity):" \
   "(smt)" \
   "(literals)" \
   "(enable-division)" \
   "(generate-programs)" \
   "(program-size):" \
   "(program-index-min):" \
   "(program-index-max):" \
   "(enumerative-solver)" \
   "(number-of-constants):" \

int main(int argc, const char *argv[])
{
  cmdlinet cmdline;
  if(cmdline.parse(argc, argv, FASTSYNTH_OPTIONS))
  {
    std::cerr << "Usage error\n";
    return 1;
  }

  if(cmdline.args.size()!=1)
  {
    std::cerr << "Usage error, file must be given\n";
    return 1;
  }

  if(cmdline.isset("generate-programs"))
  {
    if(has_suffix(cmdline.args.back(), ".sl"))
    {
      std::cout<<"Generating possible programs \n";
      generate_programs(cmdline);
      return 0;
      }
     else
      std::cerr<<"Error: generate programs must be given .sl file\n";
    return 1;
  }

  try
  {
    if(has_suffix(cmdline.args.back(), ".sl"))
      return sygus_frontend(cmdline);
    else if(has_suffix(cmdline.args.back(), ".smt2"))
      return smt2_frontend(cmdline);
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
