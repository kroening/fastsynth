/*
 * enumerative_learn.cpp
 *
 *  Created on: 29 Mar 2018
 *      Author: elipol
 */

#include "enumerative_learn.h"
#include <solvers/smt2/smt2_conv.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>
#include <langapi/language_util.h>
#include <iostream>
#include <util/simplify_expr.h>
#include <util/expr_iterator.h>

void enumerative_learnt::output_program(
    const solutiont &solution, std::ostream &out) const
{
  for(const auto &f : solution.functions)
    {
      std::string stripped_id=
              std::string(
                  id2string(f.first.get_identifier()),
                  11, std::string::npos);

            out << "C Result: "
                             << stripped_id
                             << " -> "
                             << from_expr(ns, "", f.second)
                             << '\n';
    }
}

enumerative_learnt::enumerative_learnt(
  const namespacet &_ns,
  const problemt &_problem,
  message_handlert &_message_handler):
  solver_learn_baset(_ns, _problem, _message_handler),
  program_size(1u),
  program_index(0u)
{
}

void enumerative_learnt::set_program_size(size_t program_size)
{
  if(program_size!= this->program_size)
  {
    this->program_size=program_size;
    program_index=0u;
  }
}

solutiont enumerative_learnt::get_solution() const
{
  return last_solution;
}

void enumerative_learnt::add_ce(const counterexamplet &cex)
{
  counterexamples.emplace_back(cex);
}

decision_proceduret::resultt enumerative_learnt::operator()()
{
  synth_encodingt synth_encoding;
  synth_encoding.program_size = program_size;
  synth_encoding.enable_bitwise = enable_bitwise;
  synth_encoding.literals = problem.literals;
  enumerative_assignment_generatort solver(ns, synth_encoding);

  synth_encodingt synth_encoding_verif;
  synth_encoding_verif.program_size = program_size;
  synth_encoding_verif.enable_bitwise = enable_bitwise;
  synth_encoding_verif.literals = problem.literals;

  satcheckt satcheck;
      satcheck.set_message_handler(get_message_handler());

  bv_pointerst verifier(ns, satcheck);
  verifier.set_message_handler(get_message_handler());


  if(counterexamples.empty())
  {
    synth_encoding.suffix = "$ce";
    synth_encoding.constraints.clear();

    synth_encoding_verif.suffix = "$ce";
    synth_encoding_verif.constraints.clear();


    add_problem(synth_encoding, solver);
    add_problem(synth_encoding_verif, verifier);
  }
  else
  {
    std::size_t counter = 0;
    for(const auto &c : counterexamples)
    {
      synth_encoding_verif.suffix = "$ce"+ std::to_string(counter);
      synth_encoding_verif.constraints.clear();

      add_counterexample(c, synth_encoding_verif, verifier);

      add_problem(synth_encoding_verif, verifier);
      counter++;
    }
  }
  solver.find_variables(synth_encoding);
  bool solution_found=false;

  while(!solution_found)
  {
    if(program_index > solver.number_of_options)
      return decision_proceduret::resultt::D_UNSATISFIABLE;
    solver.generate_nth_assignment(program_index);
    std::cout << "program index " << program_index
        << " program size " << program_size<<std::endl;
    program_index++;
    std::cout<<"print synth assignment\n";
    solver.print_assignment(std::cout);

    for(auto &v : solver.assignment)
    {
      if(v.second.id()==ID_constant)
      {
        std::cout<<"setting to true "<< from_expr(ns, "", v.first)<<std::endl;
        verifier.set_to(v.first, to_constant_expr(v.second).is_true());
      }
    }


    if(verifier()==decision_proceduret::resultt::D_SATISFIABLE)
    {
      std::cout<<"verified correct\n";
      last_solution = synth_encoding.get_solution(verifier);
      verifier.print_assignment(std::cout);
      output_program(last_solution, std::cout);

      return decision_proceduret::resultt::D_SATISFIABLE;
    }
  }
  return decision_proceduret::resultt::D_UNSATISFIABLE;
}

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
  PRECONDITION(assignment.count(expr)!=0);
  return assignment.at(expr);
}

void enumerative_assignment_generatort::print_assignment(
    std::ostream &out) const
{
  for(const auto & var : assignment)
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
  for(const auto &sel_vec : selector_variables)
  {
    int size_of_vec = sel_vec.size();
    // Note we do not allow constants unless added into pre configured literals.
    // to enable, use size_of_vec+1 to allow for
    // the case where no selector variables
    // are true and we use a constant
    assignment_index=local_n%(size_of_vec);
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
    local_n=local_n/(size_of_vec);
  }
}

void enumerative_assignment_generatort::find_variables(
    synth_encodingt &synth_encoding)
{
  selector_variables = synth_encoding.get_selector_variables();
  std::size_t index=0;
  for(const auto &v : synth_encoding.get_constant_variables())
  {
    irep_idt ID="constant_value"+std::to_string(index);
    assignment[v]=symbol_exprt(ID, unsignedbv_typet(32));
    index++;
  }
  number_of_options=1;
  for(const auto &sv : selector_variables)
  {
    std::cout<<"selector variable vector "<<sv.size()<<" ";
     number_of_options*=(sv.size());
     std::cout<<std::endl;
  }
  std::cout<<"number of options "<< number_of_options
      <<", program size "<< synth_encoding.program_size << "\n";


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

void enumerative_program_generatort::output_program(
    std::ostream &out, const std::size_t &index)
{
  if(index >= solver.number_of_options)
  {
    out << "Index " << index
        << " is greater than number of possible programs, which is "
        << solver.number_of_options << "\n";
    return;
  }

  solutiont solution=get_nth_program(index);
 // solver.print_assignment(out);
  out << "<program " << index << "> ";

  for(const auto &f : solution.functions)
  {
    out.setstate(std::ios_base::badbit);
    smt2_convt smt(ns, "", "", "", smt2_convt::solvert::Z3, out);
    out.clear();

    smt.convert_expr(f.second);
  }
  out << "\n</program " << index << ">\n";
}
