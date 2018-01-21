SRC = fastsynth.cpp verify_solver.cpp cegis.cpp \
      prop_learn.cpp incremental_prop_learn.cpp \
      composite_learn.cpp \
      synth_encoding.cpp verify_encoding.cpp \
      synth_encoding_constraints.cpp \
      c_frontend.cpp sygus_frontend.cpp smt2_parser.cpp \
      sygus_parser.cpp local_search.cpp

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

# MiniSAT header access is only necessary until
# https://github.com/diffblue/cbmc/pull/1750 is merged.

INCLUDES= -I $(CBMC)/src -I $(CBMC)/src/solvers/$(MINISAT2) -I ..

# Flags for MiniSAT headers. Only necessary until
# https://github.com/diffblue/cbmc/pull/1750 is merged.
CXXFLAGS += -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS

LIBS =

ifneq ($(BUILD_ENV_),MSVC)
 LIBS += -pthread
endif

CLEANFILES = fastsynth$(EXEEXT)

all: fastsynth$(EXEEXT)

###############################################################################

fastsynth$(EXEEXT): $(OBJ)
	$(LINKBIN)

