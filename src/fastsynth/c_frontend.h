/*******************************************************************\

 Module: Fastsynth ANSI-C Language Frontend

 Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_FASTSYNTH_C_FRONTEND_H
#define CPROVER_FASTSYNTH_C_FRONTEND_H

/// Interface for the synthesis of ANSI-C code. Invokes the GOTO conversion
/// of existing code and the execution of the CEGIS algorithm.
/// \param cmdline: Options coming from the command line.
/// \return 0 if successful, 1 otherwise.
int c_frontend(const class cmdlinet &cmdline);

#endif // CPROVER_FASTSYNTH_C_FRONTEND_H
