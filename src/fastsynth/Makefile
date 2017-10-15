SRC = fastsynth.cpp synth_solver.cpp verify_solver.cpp cegis.cpp

OBJ+= $(CBMC)/src/ansi-c/ansi-c$(LIBEXT) \
      $(CBMC)/src/assembler/assembler$(LIBEXT) \
      $(CBMC)/src/linking/linking$(LIBEXT) \
      $(CBMC)/src/big-int/big-int$(LIBEXT) \
      $(CBMC)/src/goto-symex/goto-symex$(LIBEXT) \
      $(CBMC)/src/goto-programs/goto-programs$(LIBEXT) \
      $(CBMC)/src/pointer-analysis/pointer-analysis$(LIBEXT) \
      $(CBMC)/src/langapi/langapi$(LIBEXT) \
      $(CBMC)/src/solvers/solvers$(LIBEXT) \
      $(CBMC)/src/analyses/dirty$(OBJEXT) \
      $(CBMC)/src/util/util$(LIBEXT)

include ../config.inc

INCLUDES= -I $(CBMC)/src -I ..

LIBS =

CLEANFILES = fastsynth$(EXEEXT)

all: fastsynth$(EXEEXT)

###############################################################################

fastsynth$(EXEEXT): $(OBJ)
	$(LINKBIN)

