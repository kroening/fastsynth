#ifndef CPROVER_CEGIS_TYPES_H_
#define CPROVER_CEGIS_TYPES_H_

#include <set>
#include <map>

#include <util/std_expr.h>

class problemt
{
public:
  std::set<exprt> free_variables;
  exprt::operandst side_conditions, constraints;
  std::set<exprt> literals; /// Constant hints for solver.
};
  
class solutiont
{
public:
  using functionst=std::map<symbol_exprt, exprt>;
  functionst functions, s_functions;
};

class counterexamplet
{
public:
  std::map<exprt, exprt> assignment;
  void clear() { assignment.clear(); }
};

#endif /* CPROVER_FASTSYNTH_SOLUTION_H_ */
