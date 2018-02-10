#include "smt2_parser.h"

#include <util/cmdline.h>
#include <util/cout_message.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/sat/satcheck.h>

#if 0
#include <util/time_stopping.h>
#include <util/config.h>

#include <ansi-c/ansi_c_language.h>

#include <langapi/language_util.h>
#include <langapi/mode.h>
#endif

#include <fstream>

class smt2_frontendt:public new_smt2_parsert
{
public:
  smt2_frontendt(
    std::ifstream &_in,
    decision_proceduret &_dest):
    new_smt2_parsert(_in),
    dest(_dest)
  {
  }

protected:
  decision_proceduret &dest;

  void command(const std::string &) override;
};

void smt2_frontendt::command(const std::string &c)
{
  if(c=="assert")
  {
    exprt e=expression();
    dest.set_to_true(e);
  }
  else
    new_smt2_parsert::command(c);
}

int smt2_frontend(const cmdlinet &cmdline)
{
  assert(cmdline.args.size()==1);

  #if 0
  register_language(new_ansi_c_language);
  config.ansi_c.set_32();
  #endif

  console_message_handlert message_handler;
  messaget message(message_handler);

  // this is our default verbosity
  unsigned int v=messaget::M_STATISTICS;

  if(cmdline.isset("verbosity"))
  {
    v=std::stol(
        cmdline.get_value("verbosity"));;
    if(v>10)
      v=10;
  }

  message_handler.set_verbosity(v);

  std::ifstream in(cmdline.args.front());

  if(!in)
  {
    message.error() << "Failed to open input file" << messaget::eom;
    return 10;
  }

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  satcheckt satcheck;
  boolbvt solver(ns, satcheck);

  satcheck.set_message_handler(message_handler);
  solver.set_message_handler(message_handler);

  smt2_frontendt smt2(in, solver);
  smt2.set_message_handler(message_handler);

  smt2.parse();

  if(!smt2)
    return 20;
  else
    return 0;
}
