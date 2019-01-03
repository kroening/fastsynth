SRC = dnnsynth_train_main.cpp

OBJ+= 

#TORCH = /opt/local/Library/Frameworks/Python.framework/Versions/3.7/lib/python3.7/site-packages/torch
TORCH = /usr/lib64/python3.5/site-packages/torch

INCLUDES= \
  -I $(TORCH)/lib/include/torch/csrc/api/include \
  -I $(TORCH)/lib/include

LIBS = -lcaffe2 -lc10 -ltorch \
       -lmkldnn $(TORCH)/lib/libgomp-7bcb08ae.so.1 \
       -L $(TORCH)/lib

include ../config.inc
include ../../$(CPROVER_DIR)/src/config.inc
include ../../$(CPROVER_DIR)/src/common

CXXFLAGS = -MMD -MP -std=c++11 -O2 -D_GLIBCXX_USE_CXX11_ABI=0

CLEANFILES = dnnsynth-train$(EXEEXT)

all: dnnsynth-train$(EXEEXT)

###############################################################################

dnnsynth-train$(EXEEXT): $(OBJ)
	$(LINKBIN)
