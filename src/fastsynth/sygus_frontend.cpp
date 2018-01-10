#include "sygus_frontend.h"
#include "sygus_parser.h"

#include <fstream>
#include <iostream>

int sygus_frontend(const cmdlinet &cmdline)
{
  assert(cmdline.args.size()==1);

  std::ifstream in(cmdline.args.front());

  if(!in)
  {
    std::cerr << "Failed to open input file\n";
    return 10;
  }

  sygus_parsert parser(in);

  parser();

  if(!parser)
    return 20;

  return 0;
}
