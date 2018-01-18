#ifndef CPROVER_FASTSYNTH_CANCELLABLE_SOLVER_H_
#define CPROVER_FASTSYNTH_CANCELLABLE_SOLVER_H_

/// Wrapper for MiniSAT solver classes exposing `interrupt`. This wrapper
/// will be removed once https://github.com/diffblue/cbmc/pull/1750 is merged.
/// \tparam solvert MiniSAT solver class to extend.
template <class solvert>
class cancellable_solvert : public solvert
{
public:
  /// Cancels the currently running SAT query.
  void cancel()
  {
    solvert::solver->interrupt();
  }

  /// Clears a previously invoked cancel operation.
  void clear()
  {
    solvert::solver->clearInterrupt();
  }
};

#endif /* CPROVER_FASTSYNTH_CANCELLABLE_SOLVER_H_ */
