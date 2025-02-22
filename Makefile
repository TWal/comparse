FSTAR_EXE ?= fstar.exe

SOURCE_DIR = src

INCLUDE_DIRS = $(SOURCE_DIR)
FSTAR_INCLUDE_DIRS = $(addprefix --include , $(INCLUDE_DIRS))

ADMIT ?=
MAYBE_ADMIT = $(if $(ADMIT),--admit_smt_queries true)

FSTAR = $(FSTAR_EXE) $(MAYBE_ADMIT)

FSTAR_EXTRACT = --extract '-* +Comparse -Comparse.Tactic'

# Allowed warnings:
# - (Warning 242) Definitions of inner let-rec ... and its enclosing top-level letbinding are not encoded to the solver, you will only be able to reason with their types
# - (Warning 335) Interface ... is admitted without an implementation 
FSTAR_FLAGS = $(FSTAR_INCLUDE_DIRS) --cache_checked_modules --already_cached '+Prims +FStar' --warn_error '@0..1000' --warn_error '+242-335' --cache_dir cache --odir obj --cmi

.PHONY: all clean

all: copy_lib

clean:
	dune clean
	rm -rf hints obj cache ml/lib/src ml/tests/src

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

cache:
	mkdir $@

obj:
	mkdir $@


%.checked: FSTAR_RULE_FLAGS=
# Comparse.Tests.TacticOutput is the only file allowing "(Warning 272) Top-level let-bindings must be total; this term may have effects"
cache/Comparse.Tests.TacticOutput.fst.checked: FSTAR_RULE_FLAGS = --warn_error '+272'

%.checked: | hints cache obj
	$(FSTAR) $(FSTAR_FLAGS) $(FSTAR_RULE_FLAGS) $< && touch -c $@

# Extraction
ALL_LIB_ML_FILES = $(filter-out obj/Comparse_Tests_%.ml,$(ALL_ML_FILES))
ALL_TEST_ML_FILES = $(filter obj/Comparse_Tests_%.ml,$(ALL_ML_FILES))

.PRECIOUS: obj/%.ml
obj/%.ml:
	$(FSTAR) $(FSTAR_FLAGS) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

.PHONY: extract_lib copy_lib

extract_lib: $(ALL_LIB_ML_FILES)

copy_lib: extract_lib
	mkdir -p ml/lib/src
	cp $(ALL_LIB_ML_FILES) ml/lib/src

%.fst-in %.fsti-in:
	@echo $(FSTAR_INCLUDE_DIRS) --include obj

# Compilation

.PHONY: extract_tests copy_tests check

extract_tests: $(ALL_TEST_ML_FILES)

copy_tests: extract_tests
	mkdir -p ml/tests/src
	cp $(ALL_TEST_ML_FILES) ml/tests/src

check: copy_lib copy_tests
	$(FSTAR_EXE) --ocamlenv dune runtest --no-buffer --profile=release
