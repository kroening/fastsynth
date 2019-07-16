/*******************************************************************\

 Module: Fastsynth Statement List Language Frontend

 Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

#ifndef CPROVER_FASTSYNTH_STATEMENT_LIST_FRONTEND_H
#define CPROVER_FASTSYNTH_STATEMENT_LIST_FRONTEND_H

/// Interface for the synthesis of Statement List code. Invokes the GOTO
/// conversion of existing code and the execution of the CEGIS algorithm.
/// \param cmdline: Options coming from the command line.
/// \return 0 if successful, 1 otherwise.
int statement_list_frontend(const class cmdlinet &cmdline);

#endif // CPROVER_FASTSYNTH_STATEMENT_LIST_FRONTEND_H
