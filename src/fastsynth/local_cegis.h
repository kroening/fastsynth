#ifndef CPROVER_FASTSYNTH_LOCAL_CEGIS_H_
#define CPROVER_FASTSYNTH_LOCAL_CEGIS_H_

#include <fastsynth/cegis.h>
#include <fastsynth/synth_encoding.h>

#include <util/namespace.h>
#include <util/symbol_table.h>

#include <memory>

/// SMT-based local solution neighbourhood search.
class local_cegist : public messaget
{
  /// Represents a neighbourhood of similar solutions.
  struct neighbourhoodt
  {
    /// Solution template representing equivalence class.
    solutiont solution;

    /// Size of all solutions in the equivalence class.
    size_t program_size;

    /// Constraints learned in local searches on this neighbourhood.
    synth_encodingt::constraintst constraints;

    /// Encoding used for the restricted CEGIS learner.
    std::unique_ptr<class synth_encoding_baset> synth_encoding;

    /// Used for restricted CEGIS learner queries on this neighbourhood.
    std::unique_ptr<class learnt> learn;

    /// Indicates whether this neighbourhood was fully explored.  This is
    /// necessary since we only complete a limited number of local CEGIS
    /// iterations at each iteration of the overall CEGIS loop.  This
    /// is effectively a manual scheduling algorithm, avoiding the need
    /// to use threads.
    bool is_complete;

    /// Indicates whether the search with just user-provided literals for
    /// constants is completed.
    bool literals_search_done;
  };

  /// \see cegist::cegist(const namespacet &)
  const namespacet &ns;

  /// \see cegist::loop(const problemt &, learnt &, verifyt &)
  verifyt &verify;

  /// \see cegist::loop(const problemt &, learnt &, verifyt &)
  const problemt &problem;

  /// All solution equivalence classes that have been or are currently
  /// being explored.
  std::vector<neighbourhoodt> solutions;

  /// Explores the given template solution locally.
  /// \param problem Associated CEGIS problem.
  /// \param neighbourhood Template solution to explore.
  void explore_neighbourhood(
    const problemt &problem,
    neighbourhoodt &neighbourhood);

  /// Adds a locally learned constraint and logs this event.
  /// \param solution Template solution for which the constraint is valid.
  /// \param constraints Constraints associated with the given template.
  /// \param constraint Newly learend constraint.
  void add_constraint(
    const solutiont &solution,
    synth_encodingt::constraintst &constraints,
    const exprt &constraint);

  /// Locates the given candidate in the list of already explored or
  /// currently being explored neighbourhoods.
  /// \param solution_template Neighbourhood to find.
  /// \return Index in solutions or <code>-1</code> if not yet explored.
  int index_of(std::map<symbol_exprt, exprt> solution_template);

  /// Index in solutions of the currently explored solution equivalence class.
  size_t solution_index;

  /// Currently explored solution equivalence class.
  solutiont current_solution;

  /// Constraints learned on the currently explored equivalence class.
  synth_encodingt::constraintst current_constraints;

public:
  /// Solution to the original CEGIS problem, if found.
  solutiont solution;

  /// \see incremental_solver_learnt
  bool incremental_solving;

  /// \see incremental_solver_learnt
  bool use_simp_solver;

  /// \see cegist::use_smt
  bool use_smt;

  /// \see cegist::logic
  std::string logic;

  /// Creates a local search which can explore solution equivalence classes
  /// for the given CEGIS problem.
  /// \param ns \see local_cegist::ns
  /// \param verify \see local_cegist::verify
  /// \param problem \see local_cegist::problem
  local_cegist(const namespacet &ns, verifyt &verify, const problemt &problem);

  /// Execute a limited number of local CEGIS iterations.
  void operator()();

  /// Create a CEGIS learner of the given type.
  /// \param synth_encoding Learner type to instantiate.
  /// \return Configured CEGIS learner.
  std::unique_ptr<learnt>
  create_learner(synth_encoding_baset &synth_encoding);

  /// Add a new neighbourhood to explore based on the given solution template.
  /// \param solution_template Template solution to explore.
  /// \param program_size Size of the given solution.
  void push_back(
    const solutiont &solution_template,
    size_t program_size);

  /// Indicates whether a solution to the overall CEGIS problem was found.
  bool has_solution();
};

#endif /* CPROVER_FASTSYNTH_LOCAL_CEGIS_H_ */
