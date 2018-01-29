#ifndef CPROVER_FASTSYNTH_LITERALS_H_
#define CPROVER_FASTSYNTH_LITERALS_H_

#include <fastsynth/cegis.h>

/// Collects all constant literals explicitly used in the problem description.
/// \param problem Problem in which to search for literals.
/// \return All constant literals located in the given problem.
std::set<constant_exprt> find_literals(const cegist::problemt &problem);

#endif /* CPROVER_FASTSYNTH_LITERALS_H_ */
