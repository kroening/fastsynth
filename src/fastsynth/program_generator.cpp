/*
 * program_generator.cpp
 *
 *  Created on: 25 Apr 2018
 *      Author: elipol
 */

#include <util/cmdline.h>
#include <util/cout_message.h>
#include <util/namespace.h>
#include <util/symbol_table.h>
#include <util/config.h>

#include <ansi-c/ansi_c_language.h>
#include <langapi/language_util.h>
#include <langapi/mode.h>

#include "enumerative_learn.h"
#include "program_generator.h"
#include "synth_encoding.h"
#include "sygus_parser.h"


#include <iostream>
#include <fstream>



int generate_programs(const cmdlinet &cmdline)
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

    problemt problem;
    problem.constraints=parser.constraints;

    for(const auto &v : parser.variable_map)
      problem.free_variables.insert(symbol_exprt(v.first, v.second));

    for(const auto &v: parser.full_let_variable_map)
      problem.free_variables.insert(symbol_exprt(v.first, v.second));

    for(auto &c : problem.constraints)
      parser.expand_function_applications(c);


  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  int program_size=4;
  int program_index_min=100;
  int program_index_max=101;


  if(cmdline.isset("program-size"))
    program_size=std::stol(
        cmdline.get_value("program-size"));
  else
    std::cout << "no program size given, "
                      <<"generating all possible programs for default size 5\n";


  if(cmdline.isset("program-index-min")&&cmdline.isset("program-index-max"))
  {
    program_index_min=std::stol(
        cmdline.get_value("program-index-min"));
    program_index_max=std::stol(
        cmdline.get_value("program-index-max"));
  }
  else
    std::cout << "program index min and program index max must be given:\n"
                      << "generating default range programs 0->9 \n";



  synth_encodingt synth_encoding;
  synth_encoding.program_size = program_size;
  synth_encoding.enable_bitwise = !cmdline.isset("no-bitwise");

  for(const auto &c: synth_encoding.constraints)
  {
    std::cout<<"constraint\n";
    std::cout<<from_expr(ns, "",c)<<std::endl<<std::endl;
  }

  enumerative_program_generatort program_generator(ns,synth_encoding, problem);

  for(int i=program_index_min; i<program_index_max; i++)
  {
    std::cout<<"Program "<< i<<"\n";
    program_generator.output_program(std::cout,i);
    std::cout<<std::flush;
  }
  return 0;
}
