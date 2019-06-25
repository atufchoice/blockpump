COQC = coqc
COQDEP = coqdep

COQ_FLAG = -Q "." Block

SOURCE := finite.v lib.v pigeonhole.v definitions.v ramsey.v lemma2choice.v lemma2nochoice.v lemma2nochoicebool.v lemma3.v toregularity.v closure.v jaffe.v
VO_FILE := $(shell find "." -type f -name '*.vo')
GLOB_FILE := $(shell find "." -type f -name '*.glob')
AUX_FILE := $(shell find "." -type f -name '*.vo.aux')

$(SOURCE:%.v=%.vo): %.vo: %.v
			@echo COQC $*.v
			@$(COQC) $(COQ_FLAG) $*.v

dep:
	@$(COQDEP) $(SOURCE) > .depend

all: $(SOURCE:%.v=%.vo)

clean:
	@rm $(VO_FILE) $(GLOB_FILE) $(AUX_FILE)

.DEFAULT_GOAL := all

include .depend
