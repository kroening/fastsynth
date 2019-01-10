SRC = dnnsynth_train_main.cpp produce_training_data.cpp train.cpp

OBJ+= 

#LIBS = -lmkldnn $(TORCH)/lib/libgomp-7bcb08ae.so.1 -lcaffe2 -lc10 -ltorch \
#       -L $(TORCH)/lib

include ../config.inc
include ../../$(CPROVER_DIR)/src/config.inc
include ../../$(CPROVER_DIR)/src/common

ifeq ($(BUILD_ENV_),OSX)
  TORCH = /opt/local/Library/Frameworks/Python.framework/Versions/3.7/lib/python3.7/site-packages/torch
else
  TORCH = /usr/lib64/python3.5/site-packages/torch
endif

LIBS = -lcaffe2 -lc10 -ltorch -L $(TORCH)/lib

INCLUDES= \
  -I $(TORCH)/lib/include/torch/csrc/api/include \
  -I $(TORCH)/lib/include

ifeq ($(BUILD_ENV_),OSX)
  CXXFLAGS = -MMD -MP -std=c++11 -O2
else
  CXXFLAGS = -MMD -MP -std=c++11 -O2 -D_GLIBCXX_USE_CXX11_ABI=0
endif

CLEANFILES = dnnsynth-train$(EXEEXT)

all: dnnsynth-train$(EXEEXT)

###############################################################################

dnnsynth-train$(EXEEXT): $(OBJ)
	$(LINKBIN)
