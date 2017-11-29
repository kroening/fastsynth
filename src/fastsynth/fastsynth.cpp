#include <iostream>

#include <util/suffix.h>
#include <util/cmdline.h>

#include "c_frontend.h"
#include "sygus_frontend.h"

int main(int argc, const char *argv[])
{
  cmdlinet cmdline;
  if(cmdline.parse(argc, argv, ""))
  {
    std::cerr << "Usage error\n";
    return 1;
  }
  
  if(cmdline.args.size()!=1)
  {
    std::cerr << "Usage error\n";
    return 1;
  }

  if(has_suffix(cmdline.args.back(), ".sl"))
    return sygus_frontend(cmdline);
  else
    return c_frontend(cmdline);
}
