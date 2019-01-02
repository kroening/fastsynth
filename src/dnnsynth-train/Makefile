SRC = dnnsynth_train_main.cpp

OBJ+= 

INCLUDES= \
  -I /opt/local//Library/Frameworks/Python.framework/Versions/3.7/lib/python3.7/site-packages/torch/lib/include/torch/csrc/api/include \
  -I /opt/local//Library/Frameworks/Python.framework/Versions/3.7/lib/python3.7/site-packages/torch/lib/include

LIBS = -lcaffe2 -lc10 -ltorch \
       -L /opt/local//Library/Frameworks/Python.framework/Versions/3.7/lib/python3.7/site-packages/torch/lib

CXXFLAGS+=-Wno-gnu-zero-variadic-macro-arguments

include ../config.inc
include ../../$(CPROVER_DIR)/src/config.inc
include ../../$(CPROVER_DIR)/src/common

CLEANFILES = dnnsynth-train$(EXEEXT)

all: dnnsynth-train$(EXEEXT)

###############################################################################

dnnsynth-train$(EXEEXT): $(OBJ)
	$(LINKBIN)
