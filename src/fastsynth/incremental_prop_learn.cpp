#include <fastsynth/incremental_prop_learn.h>
#include <fastsynth/prop_learn.h>

#include <solvers/flattening/bv_pointers.h>

incremental_prop_learnt::incremental_prop_learnt(
  const namespacet &_ns,
  const cegist::problemt &_problem,
  bool _use_simp_solver,
  message_handlert &_message_handler)
  : learnt(_message_handler),
    ns(_ns),
    problem(_problem),
    synth_satcheck(new satcheck_no_simplifiert()),
    synth_solver(new bv_pointerst(ns, *synth_satcheck)),
    program_size(1u),
    counterexample_counter(0u),
    use_simp_solver(_use_simp_solver)
{
  init();
}

void incremental_prop_learnt::init()
{
  if(use_simp_solver)
  {
    synth_satcheck.reset(new satcheckt());
    synth_solver.reset(new bv_pointerst(ns, *synth_satcheck));
  }

  synth_encoding.program_size = program_size;
  synth_satcheck->set_message_handler(get_message_handler());
  synth_solver->set_message_handler(get_message_handler());
  add_problem(ns, get_message_handler(), problem, synth_encoding, *synth_solver);
  freeze_expression_symbols();
}

void incremental_prop_learnt::set_program_size(const size_t program_size)
{
  PRECONDITION(program_size >= this->program_size);
  if(program_size == this->program_size)
    return;
  this->program_size = program_size;

  synth_satcheck.reset(new satcheck_minisat_no_simplifiert());
  synth_solver.reset(new bv_pointerst(ns, *synth_satcheck));
  synth_encoding = synth_encodingt();
  init();
  // re-add counterexamples
  if(counterexample_counter!=0u)
  {
    std::size_t counter = 0;
     for(const auto &c : counterexamples)
     {
       synth_encoding.suffix = "$ce" + std::to_string(counter);
       synth_encoding.constraints.clear();
       add_counterexample(ns, get_message_handler(), c, synth_encoding, *synth_solver);

       add_problem(ns, get_message_handler(), problem, synth_encoding, *synth_solver);

       counter++;
     }
     freeze_expression_symbols();
  }
}

decision_proceduret::resultt incremental_prop_learnt::operator()()
{
  return (*synth_solver)();
}

std::map<symbol_exprt, exprt> incremental_prop_learnt::get_expressions() const
{
  return synth_encoding.get_expressions(*synth_solver);
}

void incremental_prop_learnt::add(
  const verify_encodingt::counterexamplet &counterexample)
{
  counterexamples.emplace_back(counterexample);

  synth_encoding.constraints.clear();

  synth_encoding.suffix = "$ce" + std::to_string(counterexample_counter);

  add_counterexample(ns, get_message_handler(), counterexample, synth_encoding, *synth_solver);
  add_problem(ns, get_message_handler(), problem, synth_encoding, *synth_solver);

  freeze_expression_symbols();
  counterexample_counter++;
}

void incremental_prop_learnt::freeze_expression_symbols()
{
  if(!use_simp_solver)
    return;

  for(const auto &s : synth_solver->get_symbols())
  {
    if(id2string(s.first).find("EXPRESSION") != std::string::npos)
    {
      synth_solver->set_frozen(s.second);
    }
  }

  for(const auto &m : synth_solver->get_map().mapping)
  {
    if(id2string(m.first).find("EXPRESSION") != std::string::npos)
    {
      for(const auto &map_bit : m.second.literal_map)
        synth_solver->set_frozen(map_bit.l);
    }
  }
}

