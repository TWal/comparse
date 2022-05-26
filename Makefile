ifndef FSTAR_HOME
	FSTAR_HOME = $(dir $(shell which fstar.exe))/..
endif

include $(FSTAR_HOME)/ulib/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

SOURCE_DIR = src

INCLUDE_DIRS = $(SOURCE_DIR)
FSTAR_INCLUDE_DIRS = $(addprefix --include , $(INCLUDE_DIRS))

FSTAR_EXTRACT = --extract '-* +Comparse -Comparse.Tactic'
FSTAR_FLAGS = $(FSTAR_INCLUDE_DIRS) --cache_checked_modules --already_cached '+Prims +FStar' --warn_error '+241@247+285' --cache_dir obj --odir obj --cmi

.PHONY: all clean extract

all: extract

clean:
	rm -rf hints bin obj/*.ml obj/*.checked
	dune clean

# Dependency analysis

FSTAR_ROOTS = \
  $(wildcard $(addsuffix /*.fsti,$(SOURCE_DIR))) \
  $(wildcard $(addsuffix /*.fst,$(SOURCE_DIR)))

ifeq (,$(filter %-in,$(MAKECMDGOALS)))
ifndef MAKE_RESTARTS
.depend: .FORCE
	$(FSTAR) $(FSTAR_FLAGS) --dep full $(FSTAR_EXTRACT) $(notdir $(FSTAR_ROOTS)) > $@

.PHONY: .FORCE
.FORCE:
endif
endif

include .depend

# Verification

hints:
	mkdir $@

obj:
	mkdir $@


%.checked: FSTAR_RULE_FLAGS=

%.checked: | hints obj
	$(FSTAR) $(FSTAR_FLAGS) $(FSTAR_RULE_FLAGS) $< && touch -c $@

# Extraction

.PRECIOUS: obj/%.ml
obj/%.ml:
	$(FSTAR) $(FSTAR_FLAGS) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

extract: $(ALL_ML_FILES)

%.fst-in %.fsti-in:
	@echo $(FSTAR_INCLUDE_DIRS) --include obj
