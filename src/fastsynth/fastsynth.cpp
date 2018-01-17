#include <iostream>

#include <util/suffix.h>
#include <util/cmdline.h>

#include "c_frontend.h"
#include "sygus_frontend.h"

#define FASTSYNTH_OPTIONS \
   "(max-program-size):" \
   "(incremental)" \
   "(simplifying-solver)" \

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
    std::cerr << "Usage error\n";
    return 1;
  }

  try
  {
    if(has_suffix(cmdline.args.back(), ".sl"))
      return sygus_frontend(cmdline);
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
