#include "solver.h"

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/smt2/smt2_dec.h>

solvert::solvert(
  bool use_smt,
  const std::string &logic,
  const namespacet &_ns,
  message_handlert &message_handler)
{
  if(use_smt)
  {
    std::unique_ptr<smt2_dect> smt2_dec(new smt2_dect(
      _ns, "fastsynth", "created by fastsynth", logic, smt2_dect::solvert::Z3));
    smt2_dec->set_message_handler(message_handler);
    decision_procedure=move(smt2_dec);
  }
  else
  {
    prop=std::unique_ptr<propt>(new satcheckt(message_handler));

    decision_procedure=std::unique_ptr<decision_proceduret>(
      new bv_pointerst(_ns, *prop, message_handler));
  }
}
