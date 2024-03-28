SRC_DIRS := 'src' 'external' 'trusted'
ALL_VFILES := $(shell find $(SRC_DIRS) -not -path "external/coqutil/etc/coq-scripts/*" -name "*.v")
VFILES := $(shell find 'src' -name "*.v")
QUICK_CHECK_FILES := $(shell find 'src/program_proof/examples' -name "*.v")

# extract any global arguments for Coq from _CoqProject
COQPROJECT_ARGS := $(shell sed -E -e '/^\#/d' -e 's/-arg ([^ ]*)/\1/g' _CoqProject)
COQ_ARGS :=

# user configurable
Q:=@
TIMED:=true
TIMING_DB:=.timing.sqlite3

# We detect Coq CI via the TIMING variable (used in coq_makefile) and then
# disable the coqc.py wrapper, which doesn't work there
ifneq (,$(TIMING))
COQC := coqc
else ifeq ($(TIMED), true)
COQC := ./etc/coqc.py --timing-db $(TIMING_DB)
else
# setting TIMED to false or the empty string will disable using the wrapper,
# for environments where it doesn't work
COQC := coqc
endif

default: src/ShouldBuild.vo

all: $(VFILES:.v=.vo)
vos: src/ShouldBuild.vos
vok: $(QUICK_CHECK_FILES:.v=.vok)
interpreter: src/goose_lang/interpreter/generated_test.vos
check-assumptions: \
	src/program_proof/examples/print_assumptions.vo \
	src/program_proof/simple/print_assumptions.vo \
	src/program_proof/mvcc/print_assumptions.vo \
	src/program_proof/memkv/print_assumptions.vo \
	src/program_proof/vrsm/apps/print_assumptions.vo

.coqdeps.d: $(ALL_VFILES) _CoqProject
	@echo "COQDEP $@"
	$(Q)coqdep -vos -f _CoqProject $(ALL_VFILES) > $@

# do not try to build dependencies if cleaning or just building _CoqProject
ifeq ($(filter clean,$(MAKECMDGOALS)),)
-include .coqdeps.d
endif

# implement coq_makefile's TIMING support for Coq CI
ifneq (,$(TIMING))
TIMING_ARGS=-time
TIMING_EXT?=timing
TIMING_EXTRA = > $<.$(TIMING_EXT)
endif


%.vo: %.v _CoqProject | .coqdeps.d
	@echo "COQC $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) $(COQ_ARGS) $(TIMING_ARGS) -o $@ $< $(TIMING_EXTRA)

%.vos: %.v _CoqProject | .coqdeps.d
	@echo "COQC -vos $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) -vos $(COQ_ARGS) $< -o $@

%.vok: %.v _CoqProject | .coqdeps.d
	@echo "COQC -vok $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) $(TIMING_ARGS) -vok $(COQ_ARGS) $< -o $@

.PHONY: skip-qed unskip-qed ci

SLOW_QED_FILES := src/goose_lang/interpreter/disk_interpreter.v\
	src/goose_lang/interpreter/interpreter.v\
	src/goose_lang/logical_reln_fund.v\
	src/program_logic/crash_adequacy.v\
	src/program_logic/crash_weakestpre.v\
	src/program_logic/recovery_adequacy.v\
	src/program_logic/staged_invariant.v\
	src/program_proof/append_log_proof.v\
	src/program_proof/lockmap_proof.v\
	src/program_proof/wal/circ_proof.v\
	src/program_proof/wal/flush_proof.v\
	src/program_proof/wal/logger_proof.v\
	src/program_proof/wal/installer_proof.v\
	src/program_proof/wal/sliding_proof.v\
	src/program_proof/wal/recovery_proof.v\
	src/program_proof/obj/commit_proof.v\
	src/program_proof/txn/twophase_refinement_proof.v\
	src/program_proof/simple/setattr.v\
	src/program_proof/simple/write.v\
	src/program_proof/examples/inode_proof.v\
	src/program_proof/grove_shared/urpc_proof.v\
	src/program_proof/memkv/memkv_conditional_put_proof.v\
	src/program_proof/memkv/memkv_coord_start_proof.v\
	src/program_proof/memkv/memkv_get_proof.v\
	src/program_proof/vrsm/storage/proof.v

skip-qed:
	$(Q)./etc/disable-qed.sh $(SLOW_QED_FILES)

unskip-qed:
	$(Q)./etc/disable-qed.sh --undo $(SLOW_QED_FILES)

ci: skip-qed src/ShouldBuild.vo
	$(Q)if [ ${TIMED} = "true" ]; then \
		./etc/timing-report.py --max-files 30 --db $(TIMING_DB); \
		fi

# compiled by Coq CI
# not intended for normal development
lite: src/LiteBuild.vo
	$(Q)if [ ${TIMED} = "true" ]; then \
		./etc/timing-report.py --max-files 30 --db $(TIMING_DB); \
		fi

clean:
	@echo "CLEAN vo glob aux"
	$(Q)find $(SRC_DIRS) \( -name "*.vo" -o -name "*.vo[sk]" \
		-o -name ".*.aux" -o -name ".*.cache" -name "*.glob" \) -delete
	$(Q)rm -f .lia.cache
	$(Q)rm -f $(TIMING_DB)
	rm -f .coqdeps.d

.PHONY: default
.DELETE_ON_ERROR:
