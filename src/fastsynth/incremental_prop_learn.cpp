#include <fastsynth/incremental_prop_learn.h>

template <>
void incremental_prop_learnt<
  satcheck_no_simplifiert>::freeze_expression_symbols()
{
}

template <>
void incremental_prop_learnt<satcheckt>::freeze_expression_symbols()
{
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
