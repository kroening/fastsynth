#include "sygus_frontend.h"
#include "sygus_parser.h"
#include "cegis.h"

#include <util/cout_message.h>
#include <util/namespace.h>
#include <util/symbol_table.h>
#include <util/time_stopping.h>

#include <langapi/language_util.h>

#include <fstream>
#include <iostream>

int sygus_frontend(const cmdlinet &cmdline)
{
  assert(cmdline.args.size()==1);

  console_message_handlert message_handler;
  messaget message(message_handler);

  std::ifstream in(cmdline.args.front());

  if(!in)
  {
    message.error() << "Failed to open input file" << messaget::eom;
    return 10;
  }

  sygus_parsert parser(in);

  parser();

  if(!parser)
    return 20;

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  cegist cegis(ns);
  cegis.set_message_handler(message_handler);

  if(cmdline.isset("max-program-size"))
    cegis.max_program_size=std::stol(
      cmdline.get_value("max-program-size"));
  else
    cegis.max_program_size=5; // default

  cegist::problemt problem;
  problem.constraints=parser.constraints;

  auto start_time=current_time();

  switch(cegis(problem))
  {
  case decision_proceduret::resultt::D_SATISFIABLE:

    for(const auto &e : cegis.expressions)
    {
      message.result() << "Result: "
                       << e.first.get_identifier()
                       << " -> "
                       << from_expr(ns, "", e.second)
                       << '\n';
    }

    message.result() << messaget::eom;

    message.statistics() << "Synthesis time: "
                         << current_time()-start_time
                         << 's'
                         << messaget::eom;
    break;

  default:
    return 1;
  }

  return 0;
}
