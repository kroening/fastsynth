#include <util/cmdline.h>
#include <util/cout_message.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/sat/satcheck.h>
#include <solvers/smt2/smt2_parser.h>

#include <fstream>
#include <iostream>

class smt2_frontendt:public smt2_parsert
{
public:
  smt2_frontendt(
    std::ifstream &_in,
    decision_proceduret &_solver):
    smt2_parsert(_in),
    solver(_solver)
  {
  }

protected:
  decision_proceduret &solver;

  void command(const std::string &) override;
};

void smt2_frontendt::command(const std::string &c)
{
  if(c=="assert")
  {
    exprt e=expression();
    solver.set_to_true(e);
  }
  else if(c=="check-sat")
  {
    switch(solver())
    {
    case decision_proceduret::resultt::D_SATISFIABLE:
      std::cout << "(sat)\n";
      break;

    case decision_proceduret::resultt::D_UNSATISFIABLE:
      std::cout << "(unsat)\n";
      break;

    case decision_proceduret::resultt::D_ERROR:
      std::cout << "(error)\n";
    }
  }
  else
    smt2_parsert::command(c);
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

  try
  {
    smt2.parse();
    return 0;
  }
  catch(const smt2_tokenizert::smt2_errort &error)
  {
    message.error() << error.get_line_no() << ": "
                    << error.what() << messaget::eom;
    return 20;
  }
  catch(...)
  {
    return 20;
  }
}
