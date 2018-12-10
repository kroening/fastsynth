#ifndef CPROVER_FASTSYNTH_CEGIS_TYPES_H_
#define CPROVER_FASTSYNTH_CEGIS_TYPES_H_

#include <set>
#include <map>

#include <util/std_expr.h>

class problemt
{
public:
  std::set<exprt> free_variables;
  exprt::operandst side_conditions, constraints;
  std::set<constant_exprt> literals; /// Constant hints for solver.
};

class solutiont
{
public:
  #if 0
  struct functiont
  {
    mathematical_function_typet signature;
    exprt body;
  };

  // map from function identifiers
  using functionst=std::map<irep_idt, functiont>;

  functionst functions;
  functionst s_functions; // symbolic encoding
  #endif

  using functionst=std::map<symbol_exprt, exprt>;
  functionst functions, s_functions;
};

class counterexamplet
{
public:
  std::map<exprt, exprt> assignment;
  void clear() { assignment.clear(); }
};

#endif /* CPROVER_FASTSYNTH_CEGIS_TYPES_H_ */
