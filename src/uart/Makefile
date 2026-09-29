# Copyright 2026 Google LLC (chipsalliance project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
.PHONY: compile run cov_report clean vcs verdi

SHELL   = bash
PYTHON ?= python3

# Allow tool override
TEST ?= uart_base_test
SEQ  ?= uart_smoke_vseq
SEED ?= 1
COV  ?= 0

# Check for CALIPTRA_SS_ROOT
ifeq (,$(wildcard ${CALIPTRA_SS_ROOT}/src/uart))
$(error env var CALIPTRA_SS_ROOT does not point to a valid dir! Exiting!)
endif

# Optional REG_DIR for grouping compile, runs, coverage, and summary
ifneq ($(REG_DIR),)
  BUILD_DIR ?= $(REG_DIR)/build_vcs
  COV_DIR   ?= $(CURDIR)/$(REG_DIR)/cov_db.vdb
  COV_REPORT_DIR ?= $(CURDIR)/$(REG_DIR)/cov_report
  RUN_BASE_DIR := $(REG_DIR)/
else
  BUILD_DIR ?= build_vcs
  COV_DIR   ?= $(CURDIR)/cov_db.vdb
  COV_REPORT_DIR ?= $(CURDIR)/cov_report
  RUN_BASE_DIR :=
endif

# Handle SEED parameter and run directory naming (<seedno>.run_<seq_name>)
ifneq ($(SEED),)
  ifeq ($(filter $(SEED),random auto),$(SEED))
    SEED_ARG := +ntb_random_seed_automatic
    RUN_DIR  := $(RUN_BASE_DIR)$(SEED).run_$(SEQ)
  else
    SEED_ARG := +ntb_random_seed=$(SEED)
    RUN_DIR  := $(RUN_BASE_DIR)$(SEED).run_$(SEQ)
  endif
else
  SEED_ARG :=
  RUN_DIR  := $(RUN_BASE_DIR)1.run_$(SEQ)
endif

# Coverage flags
ifneq ($(filter 1, $(COV)),)
  VCS_COV_BUILD = -cm line+cond+fsm+tgl+branch+assert -cm_seqnoconst -cm_dir $(COV_DIR)
  VCS_COV_RUN   = -cm line+cond+fsm+tgl+branch+assert -cm_dir $(COV_DIR) -cm_name $(SEQ)_seed$(SEED) +en_cov=1
endif

ifneq ($(filter 1, $(WAVES) $(DUMP) $(DEBUG)),)
 VCS_DEBUG = -debug_access+all -kdb +memcbk +define+VCS_DEBUG
endif

LATEST_RUN = $(shell ls -td $(RUN_BASE_DIR)*run_* 2>/dev/null | head -n 1)

clean:
	rm -rf simv* *.log csrc ucli.key vc_hdrs.h $(BUILD_DIR)

# Target: Compile ONCE into $(BUILD_DIR)/simv
compile:
	mkdir -p $(BUILD_DIR)
	cd $(BUILD_DIR) && 	vcs -licwait 30 $(VCS_DEBUG) $(VCS_COV_BUILD) -sverilog -full64 -ntb_opts uvm-1.2 		+define+SIMULATION +define+INC_ASSERT +define+DISABLE_ALERT_SVA 		+define+UVM +define+UVM_NO_DEPRECATED +define+UVM_REGEX_NO_DPI 		+define+UVM_REG_ADDR_WIDTH=32 +define+UVM_REG_DATA_WIDTH=32 		-timescale=1ns/1ps -notice 		-kdb -debug_access+all 		-top tb -f ${CALIPTRA_SS_ROOT}/src/uart/config/uart_tb_flat.vf 		-o simv -l compile.log

# Target: Run a sequence using pre-compiled simv
run:
	@if [ ! -f $(BUILD_DIR)/simv ]; then 		echo "Executable $(BUILD_DIR)/simv not found! Compiling first..."; 		$(MAKE) compile WAVES=1 $(if $(REG_DIR),REG_DIR=$(REG_DIR),) $(if $(filter 1,$(COV)),COV=1,); 	fi
	mkdir -p $(RUN_DIR)
	cd $(RUN_DIR) && 	ln -sf $(CURDIR)/$(BUILD_DIR)/simv . && 	ln -sf $(CURDIR)/$(BUILD_DIR)/simv.daidir . && 	./simv +vcs+lic+wait +fsdb+mda +fsdb+mda_depth=0 +fsdb+struct -l vcs.log 		+UVM_TESTNAME=${TEST} +UVM_TEST_SEQ=${SEQ} $(SEED_ARG) $(VCS_COV_RUN) $(EXTRA_ARGS) $(ARGS)

cov_report:
	@echo "Generating coverage report with urg from $(COV_DIR)..."
	mkdir -p $(COV_REPORT_DIR)
	urg -full64 -dir $(COV_DIR) -format both -report $(COV_REPORT_DIR) -show tests -elfile $(CURDIR)/dv/cov/uart_cov_excl.el -excl_bypass_checks
	@echo "Coverage report generated at $(COV_REPORT_DIR)/dashboard.html and $(COV_REPORT_DIR)/hierarchy.txt"

# Backward-compatibility target: Compile and run together
vcs: compile run

verdi:
	@if [ -n "$(LATEST_RUN)" ]; then 		echo "Opening Verdi for $(LATEST_RUN)..."; 		verdi -dbdir $(LATEST_RUN)/simv.daidir -ssf $(LATEST_RUN)/dump.fsdb & 	else 		echo "No run directory found!"; 	fi
