#include "sygus_frontend.h"
#include "sygus_parser.h"
#include "cegis.h"
#include "literals.h"

#include <util/cout_message.h>
#include <util/namespace.h>
#include <util/symbol_table.h>
#include <util/config.h>

#include <ansi-c/ansi_c_language.h>

#include <solvers/smt2/smt2_conv.h>

#include <langapi/language_util.h>
#include <langapi/mode.h>

#include <fstream>
#include <chrono>

int sygus_frontend(const cmdlinet &cmdline)
{
  assert(cmdline.args.size()==1);

  register_language(new_ansi_c_language);
  config.ansi_c.set_32();

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

  sygus_parsert parser(in);
  parser.set_message_handler(message_handler);

  parser.parse();

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

  cegis.incremental_solving=cmdline.isset("incremental");
  cegis.enumerative_engine=cmdline.isset("enumerative-solver");
  cegis.use_simp_solver=cmdline.isset("simplifying-solver");
  cegis.use_fm=cmdline.isset("fm");
  cegis.enable_bitwise=!cmdline.isset("no-bitwise");
  cegis.use_smt=cmdline.isset("smt");
  cegis.enable_division=cmdline.isset("enable-division");
  cegis.logic=parser.logic;

  problemt problem;
  problem.constraints=parser.constraints;

  for(const auto &v : parser.variable_map)
    problem.free_variables.insert(symbol_exprt(v.first, v.second));

  for(const auto &v: parser.full_let_variable_map)
    problem.free_variables.insert(symbol_exprt(v.first, v.second));

  for(auto &c : problem.constraints)
    parser.expand_function_applications(c);

  if(cmdline.isset("literals"))
    problem.literals=find_literals(problem);

  auto start_time=std::chrono::steady_clock::now();

  switch(cegis(problem))
  {
  case decision_proceduret::resultt::D_SATISFIABLE:

    for(const auto &f : cegis.solution.functions)
    {
      std::string stripped_id=
        std::string(id2string(f.first.get_identifier()), 11, std::string::npos);

      message.result() << "Result: "
                       << stripped_id
                       << " -> "
                       << from_expr(ns, "", f.second)
                       << '\n';

      smt2_convt smt(ns, "", "", "", smt2_convt::solvert::Z3, message.result());
      message.result() << "SMT: "
                       << f.first.get_identifier()
                       << " -> ";
      smt.convert_expr(f.second);

      message.result() << '\n';
    }

    message.result() << messaget::eom;

    message.statistics() << "Synthesis time: "
                         << std::chrono::duration<double>(
                               std::chrono::steady_clock::now()-start_time).count()
                         << 's'
                         << messaget::eom;
    break;

  default:
    return 1;
  }

  return 0;
}
