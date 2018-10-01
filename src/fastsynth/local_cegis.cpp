#include <fastsynth/local_cegis.h>
#include <fastsynth/constant_limits.h>
#include <fastsynth/incremental_solver_learn.h>
#include <fastsynth/local_synth_encoding.h>
#include <fastsynth/solver_learn.h>

#include <langapi/language_util.h>

#include <util/arith_tools.h>
#include <util/make_unique.h>

#include <iterator>

local_cegist::local_cegist(
  const namespacet &ns,
  verifyt &verify,
  const problemt &problem)
  : ns(ns),
    verify(verify),
    problem(problem),
    solution_index(0),
    incremental_solving(false),
    use_simp_solver(false),
    use_smt(true)
{
}

namespace
{
/// Helper class to access protected cegist operations.
class cegis_accessort : public cegist
{
public:
  /// \see cegsit::loop(const problemt &, learnt &, verifyt &)
  decision_proceduret::resultt
  loop(const problemt &problem, learnt &learn, verifyt &verify)
  {
    return cegist::loop(problem, learn, verify);
  }
};
} // namespace

void local_cegist::explore_neighbourhood(
  const problemt &problem,
  neighbourhoodt &neighbourhood)
{
  if(neighbourhood.is_complete)
    return;
  const solutiont &candidate = neighbourhood.solution;

  debug() << "Local search on candidate: \n";
  output_expressions(candidate.functions, ns, debug());
  debug() << eom;

  // First run local_synth_encodingt with literals only.
  if(!problem.literals.empty() && !neighbourhood.literals_search_done)
  {
    neighbourhood.literals_search_done = true;

    debug() << "Local search on literals...\n" << eom;
    cegist literal_cegis(ns);
    literal_cegis.set_message_handler(get_message_handler());
    literal_cegis.incremental_solving = incremental_solving;
    literal_cegis.use_simp_solver = use_simp_solver;
    literal_cegis.use_local_search = false;
    literal_cegis.min_program_size = neighbourhood.program_size;
    literal_cegis.max_program_size = literal_cegis.min_program_size;
    current_solution = candidate;
    current_constraints.clear();

    local_synth_encodingt synth_encoding(
      ns, current_solution, current_constraints);
    synth_encoding.literals = problem.literals;

    const std::unique_ptr<learnt> learn(create_learner(synth_encoding));

    cegis_accessort &loop = static_cast<cegis_accessort &>(literal_cegis);
    const decision_proceduret::resultt lit_result =
      loop.loop(problem, *learn, verify);
    debug() << "Finished Local search on literals...\n" << eom;
    if(decision_proceduret::resultt::D_SATISFIABLE == lit_result)
    {
      debug() << "Local search on literals successful\n" << eom;
      solution = literal_cegis.solution;
      neighbourhood.is_complete = true;
      return;
    }
  }

  // Generate constraints using SMT.
  message_handlert &msg = get_message_handler();
  constant_limitst limits(msg, ns, problem, candidate);
  const decision_proceduret::resultt literals_result = limits(candidate);
  switch(literals_result)
  {
  case decision_proceduret::resultt::D_SATISFIABLE:
    solution = limits.solution;
  case decision_proceduret::resultt::D_UNSATISFIABLE:
    neighbourhood.is_complete = true;
    return;
  case decision_proceduret::resultt::D_ERROR:
    copy(
      begin(limits.result_constraints),
      end(limits.result_constraints),
      back_inserter(neighbourhood.constraints));
  }

  // Run regular CEGIS loop with local_synth_encodingt
  cegist cegis(ns);
  cegis.set_message_handler(get_message_handler());
  cegis.incremental_solving = incremental_solving;
  cegis.use_simp_solver = use_simp_solver;
  cegis.use_smt = use_smt;
  cegis.logic = logic;
  cegis.use_local_search = false;
  cegis.min_program_size = neighbourhood.program_size;
  cegis.max_program_size = cegis.min_program_size;
  cegis.max_iterations = 10u;
  learnt &learn = *neighbourhood.learn;
  current_solution = candidate;
  current_constraints = neighbourhood.constraints;

  cegis_accessort &loop = static_cast<cegis_accessort &>(cegis);
  const decision_proceduret::resultt result = loop.loop(problem, learn, verify);
  switch(result)
  {
  case decision_proceduret::resultt::D_SATISFIABLE:
    solution = cegis.solution;
  case decision_proceduret::resultt::D_UNSATISFIABLE:
    neighbourhood.is_complete = true;
    break;
  case decision_proceduret::resultt::D_ERROR:
    neighbourhood.solution = cegis.solution;
  }
}

void local_cegist::operator()()
{
  neighbourhoodt &neighbourhood = solutions[solution_index];
  explore_neighbourhood(problem, neighbourhood);

  debug() << "Finished limited local search on solution: \n";
  output_expressions(neighbourhood.solution.functions, ns, debug());
  debug() << eom;
}

void local_cegist::add_constraint(
  const solutiont &solution,
  synth_encodingt::constraintst &constraints,
  const exprt &constraint)
{
  debug() << "Learned new constraint: " << from_expr(ns, "", constraint);
  debug() << "\nfor solution: ";
  output_expressions(solution.functions, ns, debug());
  debug() << eom;
  constraints.emplace_back(constraint);
}

/// Helper to set all literal constants in a solution to zero. This makes
/// solution templates comparable.
class clear_constantst : public expr_visitort
{
public:
  /// expr_visitort::operator()(exprt &)
  void operator()(exprt &expr) override
  {
    if(ID_constant != expr.id())
      return;
    expr = from_integer(0u, expr.type());
  }
};

/// \see clear_constantst
static void clear_constants(std::map<symbol_exprt, exprt> &solution)
{
  clear_constantst clear;
  for(auto &expr : solution)
    expr.second.visit(clear);
}

int local_cegist::index_of(std::map<symbol_exprt, exprt> solution)
{
  clear_constants(solution);
  for(size_t i = 0; i < solutions.size(); ++i)
  {
    std::map<symbol_exprt, exprt> rhs(solutions[i].solution.functions);
    clear_constants(rhs);
    if(solution == rhs)
      return static_cast<int>(i);
  }
  return -1;
}

std::unique_ptr<learnt>
local_cegist::create_learner(synth_encoding_baset &synth_encoding)
{
  message_handlert &msg = get_message_handler();

  if(incremental_solving)
  {
    return std::unique_ptr<learnt>(new incremental_solver_learnt(
      ns, problem, synth_encoding, use_simp_solver, msg));
  }
  else
  {
    std::unique_ptr<solver_learnt> learn(
      new solver_learnt(ns, problem, synth_encoding, msg));
    learn->use_smt = use_smt;
    learn->logic = logic;
    return learn;
  }
}

void local_cegist::push_back(
  const solutiont &solution_template,
  const size_t program_size)
{
  const solutiont::functionst &functions = solution_template.functions;
  debug() << "New solution for local search:\n";
  output_expressions(functions, ns, debug());
  debug() << eom;

  int solution_index = index_of(functions);
  if(solution_index != -1)
  {
    this->solution_index = static_cast<size_t>(solution_index);
    return;
  }

  debug() << "Scheduling new local search:\n";
  output_expressions(functions, ns, debug());
  debug() << eom;

  this->solution_index = solutions.size();
  neighbourhoodt neighbourhood;
  neighbourhood.solution = solution_template;
  neighbourhood.program_size = program_size;
  neighbourhood.is_complete = false;
  neighbourhood.literals_search_done = false;
  neighbourhood.synth_encoding = util_make_unique<local_synth_encodingt>(
    ns, current_solution, current_constraints);
  neighbourhood.learn = create_learner(*neighbourhood.synth_encoding);
  solutions.emplace_back(std::move(neighbourhood));
}

bool local_cegist::has_solution()
{
  return !solution.functions.empty();
}
