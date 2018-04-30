/*
 * enumerative_learn.cpp
 *
 *  Created on: 29 Mar 2018
 *      Author: elipol
 */

#include "enumerative_learn.h"
#include <solvers/smt2/smt2_conv.h>
#include <langapi/language_util.h>
#include <iostream>


void enumerative_assignment_generatort::set_to_true(const exprt &expr)
{
    assignment[expr]=true_exprt();
}

void enumerative_assignment_generatort::set_to(const exprt &expr, bool value)
{
  if(value)
    assignment[expr]=true_exprt();
  else
    assignment[expr]=false_exprt();
}

exprt enumerative_assignment_generatort::get(const exprt &expr) const
{
  assert(assignment.count(expr)!=0);
  return assignment.at(expr);
}

void enumerative_assignment_generatort::print_assignment(std::ostream &out) const
{
  for(const auto & var: assignment)
  {
    out<<from_expr(ns, "", var.first) << " ";
    out<<from_expr(ns, "", var.second) << "\n";
  }
}

std::string enumerative_assignment_generatort::decision_procedure_text() const
{
  return "enumerative solver implemented for CEGIS\n";
}


void enumerative_assignment_generatort::generate_nth_assignment(std::size_t n)
{
  std::size_t assignment_index=n+1; // don't do anything with index 0
  std::size_t local_n=n;
  for(const auto &sel_vec: selector_variables)
  {
    int size_of_vec = sel_vec.size();
    assignment_index=local_n%size_of_vec;

    for(std::size_t i=0; i<sel_vec.size(); i++)
    {
      if(i==assignment_index)
      {
        assignment[sel_vec[i]]=true_exprt();
        get(sel_vec[i]);
      }
      else
      {
        assignment[sel_vec[i]]=false_exprt();
      }
    }
    local_n=local_n/size_of_vec;
  }

}

void enumerative_assignment_generatort::find_variables(
    synth_encodingt &synth_encoding)
{
   selector_variables = synth_encoding.get_selector_variables();
   for(const auto &v: synth_encoding.get_constant_variables())
   {
     assignment[v]=constant_exprt("CONST",unsignedbv_typet(32));
   }
}


solutiont enumerative_program_generatort::get_nth_program(const std::size_t &n)
{
  solver.generate_nth_assignment(n);
  return synth_encoding.get_solution(solver);
}

void enumerative_program_generatort::set_up(problemt &problem)
{
  for(const exprt &e : problem.side_conditions)
   {
     const exprt encoded = synth_encoding(e);
     solver.set_to_true(encoded);
   }

   for(const auto &e : problem.constraints)
   {
     const exprt encoded = synth_encoding(e);
     solver.set_to_true(encoded);
   }

   for(const auto &c : synth_encoding.constraints)
   {
     solver.set_to_true(c);
   }
  solver.find_variables(synth_encoding);
}

void enumerative_program_generatort::output_program(std::ostream &out, const std::size_t &index)
{
  solutiont solution=get_nth_program(index);

  out<<"<program "<< index << ">\n";

  for(const auto &f: solution.functions)
  {
    std::string stripped_id=
            std::string(id2string(f.first.get_identifier()), 11, std::string::npos);

          out << "C Result: "
                           << stripped_id
                           << " -> "
                           << from_expr(ns, "", f.second)
                           << '\n';

          smt2_convt smt(ns, "", "", "", smt2_convt::solvert::Z3, out);
          out << "SMT Result:  "
                           << stripped_id
                           << " -> ";
          smt.convert_expr(f.second);
          out << '\n';
  }
  out <<"</program " << index << ">\n";
}


