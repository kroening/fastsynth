#include <fastsynth/synth_encoding_constraints.h>
#include <fastsynth/synth_encoding.h>

#include <langapi/language_util.h>

#include <solvers/prop/prop_conv.h>

void add_counterexample(
  const namespacet &ns,
  messaget &msg,
  const verify_encodingt::counterexamplet &ce,
  synth_encodingt &synth_encoding,
  prop_convt &prop_conv)
{
  for(const auto &it : ce)
  {
    const exprt &symbol = it.first;
    const exprt &value = it.second;

    exprt encoded = synth_encoding(equal_exprt(symbol, value));
    msg.debug() << "ce: " << from_expr(ns, "", encoded) << messaget::eom;
    prop_conv.set_to_true(encoded);
  }
}

void generate_constraint(
  const namespacet &ns,
  messaget &msg,
  const cegist::problemt &problem,
  const std::vector<verify_encodingt::counterexamplet> &counterexamples,
  synth_encodingt &synth_encoding,
  prop_convt &prop_conv)
{
  if(counterexamples.empty())
  {
    synth_encoding.suffix = "$ce";
    synth_encoding.constraints.clear();

    add_problem(ns, msg, problem, synth_encoding, prop_conv);
  }
  else
  {
    std::size_t counter = 0u;
    for(const verify_encodingt::counterexamplet &ce : counterexamples)
    {
      synth_encoding.suffix = "$ce" + std::to_string(counter++);
      synth_encoding.constraints.clear();

      add_counterexample(ns, msg, ce, synth_encoding, prop_conv);
      add_problem(ns, msg, problem, synth_encoding, prop_conv);
    }
  }
}

void add_problem(
  const namespacet &ns,
  messaget &msg,
  const cegist::problemt &problem,
  synth_encodingt &encoding,
  prop_convt &prop_conv)
{
  for(const exprt &e : problem.side_conditions)
  {
    const exprt encoded = encoding(e);
    msg.debug() << "sc: " << from_expr(ns, "", encoded) << messaget::eom;
    prop_conv.set_to_true(encoded);
  }

  for(const auto &e : problem.constraints)
  {
    const exprt encoded = encoding(e);
    msg.debug() << "co: " << from_expr(ns, "", encoded) << messaget::eom;
    prop_conv.set_to_true(encoded);
  }

  for(const auto &c : encoding.constraints)
  {
    prop_conv.set_to_true(c);
    msg.debug() << "ec: " << from_expr(ns, "", c) << messaget::eom;
  }
}
