#include <fastsynth/local_search.h>

local_learnt::local_learnt(learnt &learn) : learn(learn)
{
}

void local_learnt::set_program_size(const size_t program_size)
{
}

decision_proceduret::resultt local_learnt::operator()()
{
  return decision_proceduret::resultt::D_ERROR;
}

std::map<symbol_exprt, exprt> local_learnt::get_expressions() const
{
  return std::map<symbol_exprt, exprt>();
}

void local_learnt::add(const verify_encodingt::counterexamplet &counterexample)
{
  learn.add(counterexample);
}
