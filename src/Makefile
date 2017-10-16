SUBDIRS = fastsynth

#CPROVER_DIR = lib/cbmc/src
#export CPROVER_DIR

all: fastsynth

.PHONY: $(SUBDIRS)
.PHONY: clean

$(SUBDIRS):
	$(MAKE) -C $@

# Dependencies

fastsynth: 

# building cbmc proper
.PHONY: cprover.dir
cprover:
	$(MAKE) $(MAKEARGS) -C ../$(CPROVER_DIR)

clean: $(patsubst %, %_clean, $(SUBDIRS))

$(patsubst %, %_clean, $(SUBDIRS)):
	if [ -e $(patsubst %_clean, %, $@)/. ] ; then \
	        $(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \
	fi

