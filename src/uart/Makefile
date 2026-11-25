# Copyright 2026 Google LLC (chipsalliance project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
.PHONY: compile run cov_report clean vcs verdi smoke

SHELL   = bash
PYTHON ?= python3

# Allow tool override
TEST     ?= uart_base_test
SEQ      ?= uart_smoke_vseq
RUN_NAME ?= $(SEQ)
SEED     ?= 1
COV      ?= 0

# Check for CALIPTRA_SS_ROOT and validate CALIPTRA_ROOT (note: flake.nix sets CALIPTRA_ROOT to caliptra-ss root)
ifeq (,$(wildcard ${CALIPTRA_SS_ROOT}/src/uart))
$(error env var CALIPTRA_SS_ROOT does not point to a valid dir! Exiting!)
endif
ifeq (,$(wildcard ${CALIPTRA_ROOT}/src/caliptra_prim))
  override CALIPTRA_ROOT := ${CALIPTRA_SS_ROOT}/third_party/caliptra-rtl
endif
ifeq (,$(wildcard ${CALIPTRA_ROOT}/src/caliptra_prim))
$(error env var CALIPTRA_ROOT (${CALIPTRA_ROOT}) does not contain src/caliptra_prim; ensure third_party/caliptra-rtl submodule is initialized!)
endif
export CALIPTRA_ROOT

# Optional REG_DIR for grouping compile, runs, coverage, and summary
ifneq ($(REG_DIR),)
  BUILD_DIR ?= $(REG_DIR)/build_vcs
  COV_DIR   ?= $(abspath $(REG_DIR))/cov_db.vdb
  COV_REPORT_DIR ?= $(abspath $(REG_DIR))/cov_report
  RUN_BASE_DIR := $(REG_DIR)/
else
  BUILD_DIR ?= build_vcs
  COV_DIR   ?= $(CURDIR)/cov_db.vdb
  COV_REPORT_DIR ?= $(CURDIR)/cov_report
  RUN_BASE_DIR :=
endif

# Handle SEED parameter and run directory naming (<seedno>.run_<run_name>)
ifneq ($(SEED),)
  ifeq ($(filter $(SEED),random auto),$(SEED))
    RAND_TAG     := $(shell date +%s%N | cut -c1-13)
    SEED_ARG     := +ntb_random_seed_automatic
    RUN_DIR      := $(RUN_BASE_DIR)$(SEED)_$(RAND_TAG).run_$(RUN_NAME)
    CM_TEST_NAME := $(RUN_NAME)_seed$(SEED)_$(RAND_TAG)
  else
    SEED_ARG     := +ntb_random_seed=$(SEED)
    RUN_DIR      := $(RUN_BASE_DIR)$(SEED).run_$(RUN_NAME)
    CM_TEST_NAME := $(RUN_NAME)_seed$(SEED)
  endif
else
  SEED_ARG     :=
  RUN_DIR      := $(RUN_BASE_DIR)1.run_$(RUN_NAME)
  CM_TEST_NAME := $(RUN_NAME)_seed1
endif

# Coverage flags (aligned with dvsim cover.cfg + common_cov_excl.cfg + uart_cover.cfg).
# Fall back to ${CALIPTRA_ROOT}/tools/dvsim/tools/vcs when the nix develop symlink tools/dvsim is absent.
ifneq ($(filter 1, $(COV)),)
  DVSIM_VCS_DIR = $(if $(wildcard ${CALIPTRA_SS_ROOT}/tools/dvsim/tools/vcs/cover.cfg),${CALIPTRA_SS_ROOT}/tools/dvsim/tools/vcs,${CALIPTRA_ROOT}/tools/dvsim/tools/vcs)
  ifeq (,$(wildcard $(DVSIM_VCS_DIR)/cover.cfg))
    $(error Missing $(DVSIM_VCS_DIR)/cover.cfg required by VCS -cm_hier (DUT-only +tree tb.dut is supplied by dv/cov/uart_cover.cfg)!)
  endif
  VCS_COV_HIER_FILES = $(DVSIM_VCS_DIR)/cover.cfg+$(DVSIM_VCS_DIR)/common_cov_excl.cfg+$(CURDIR)/dv/cov/uart_cover.cfg
  VCS_COV_FSM_FILTER = $(if $(wildcard $(DVSIM_VCS_DIR)/fsm_reset_cov.cfg),-cm_fsmresetfilter $(DVSIM_VCS_DIR)/fsm_reset_cov.cfg,)
  VCS_COV_BUILD = -lca -cm line+cond+fsm+tgl+branch+assert -cm_hier $(VCS_COV_HIER_FILES) -cm_common_hier -cm_line contassign -cm_tgl mda+structarr+portsonly -cm_cond for -cm_report noinitial -cm_seqnoconst -diag noconst -cm_glitch 0 +warn=noVCM-OPTIGN $(VCS_COV_FSM_FILTER) -cm_dir $(COV_DIR)
  VCS_COV_RUN   = -lca -cm line+cond+fsm+tgl+branch+assert -cm_dir $(COV_DIR) -cm_name $(CM_TEST_NAME) +en_cov=1
endif

ifneq ($(filter 1, $(WAVES) $(DUMP) $(DEBUG)),)
  VCS_DEBUG     = -debug_access+all -kdb +memcbk +define+VCS_DEBUG
  VCS_RUN_WAVES = +fsdb+mda +fsdb+mda_depth=0 +fsdb+struct
endif

LATEST_RUN = $(shell ls -td $(RUN_BASE_DIR)*run_* 2>/dev/null | head -n 1)

clean:
	rm -rf simv* *.log csrc ucli.key vc_hdrs.h $(BUILD_DIR) $(RUN_BASE_DIR)*run_* $(COV_DIR) $(COV_REPORT_DIR)

# Target: Compile ONCE into $(BUILD_DIR)/simv
compile:
	mkdir -p $(BUILD_DIR)
	@rm -f $(BUILD_DIR)/.waves_enabled $(BUILD_DIR)/.cov_enabled
	cd $(BUILD_DIR) && \
	vcs -licqueue $(VCS_DEBUG) $(VCS_COV_BUILD) -sverilog -full64 -ntb_opts uvm-1.2 \
		+define+SIMULATION +define+INC_ASSERT +define+CLP_ASSERT_ON \
		+define+UVM +define+UVM_NO_DEPRECATED +define+UVM_REGEX_NO_DPI \
		+define+UVM_REG_ADDR_WIDTH=32 +define+UVM_REG_DATA_WIDTH=32 +define+UVM_REG_BYTENABLE_WIDTH=4 \
		+define+DUT_HIER=tb.dut -assert svaext -assert dbgopt \
		-timescale=1ns/1ps -notice \
		-top tb -f ${CALIPTRA_SS_ROOT}/src/uart/config/uart_tb_flat.vf \
		-o simv -l compile.log
	@if [ -n "$(VCS_DEBUG)" ]; then touch $(BUILD_DIR)/.waves_enabled; fi
	@if [ -n "$(VCS_COV_BUILD)" ]; then touch $(BUILD_DIR)/.cov_enabled; fi

# Target: Run a sequence using pre-compiled simv (fails closed with non-zero exit code on any UVM/SVA error; zero retries)
run:
	@if [ ! -f $(BUILD_DIR)/simv ] || \
	    ( [ -n "$(VCS_DEBUG)" ] && [ ! -f $(BUILD_DIR)/.waves_enabled ] ) || \
	    ( [ -z "$(VCS_DEBUG)" ] && [ -f $(BUILD_DIR)/.waves_enabled ] ) || \
	    ( [ -n "$(VCS_COV_RUN)" ] && [ ! -f $(BUILD_DIR)/.cov_enabled ] ) || \
	    ( [ -z "$(VCS_COV_RUN)" ] && [ -f $(BUILD_DIR)/.cov_enabled ] ); then \
		echo "Compiling $(BUILD_DIR)/simv with requested debug/coverage flags..."; \
		$(MAKE) compile $(if $(VCS_DEBUG),WAVES=1,) $(if $(REG_DIR),REG_DIR=$(REG_DIR),) $(if $(filter 1,$(COV)),COV=1,); \
	fi
	mkdir -p $(RUN_DIR)
	cd $(RUN_DIR) && \
	ln -sf $(abspath $(BUILD_DIR))/simv . && \
	ln -sf $(abspath $(BUILD_DIR))/simv.daidir . && \
	./simv -licqueue +cdc_instrumentation_enabled=1 $(VCS_RUN_WAVES) -l vcs.log \
		+UVM_TESTNAME=${TEST} +UVM_TEST_SEQ=${SEQ} $(SEED_ARG) $(VCS_COV_RUN) $(EXTRA_ARGS) $(ARGS) && \
	grep -q "TEST PASSED" vcs.log && \
	! grep -q "TEST FAILED" vcs.log && \
	! grep -Eq "^[[:space:]]*Offending '" vcs.log && \
	grep -Eq "^UVM_ERROR :[[:space:]]*0$$" vcs.log && \
	grep -Eq "^UVM_FATAL :[[:space:]]*0$$" vcs.log

cov_report:
	@echo "Generating coverage report with urg from $(COV_DIR)..."
	mkdir -p $(COV_REPORT_DIR)
	urg -lca -full64 +urg+lic+wait -dir $(COV_DIR) -format both -report $(COV_REPORT_DIR) -show tests -elfile $(CURDIR)/dv/cov/uart_cov_excl.el
	@echo "Coverage report generated at $(COV_REPORT_DIR)/dashboard.html and $(COV_REPORT_DIR)/hierarchy.txt"

# Backward-compatibility target: Compile and run together (enables WAVES=1 by default so `make verdi` works directly)
vcs:
	$(MAKE) compile WAVES=$(if $(WAVES),$(WAVES),1) $(if $(REG_DIR),REG_DIR=$(REG_DIR),) $(if $(filter 1,$(COV)),COV=1,)
	$(MAKE) run WAVES=$(if $(WAVES),$(WAVES),1) TEST=$(TEST) SEQ=$(SEQ) RUN_NAME=$(RUN_NAME) SEED=$(SEED) $(if $(REG_DIR),REG_DIR=$(REG_DIR),) $(if $(filter 1,$(COV)),COV=1,) EXTRA_ARGS="$(EXTRA_ARGS)" ARGS="$(ARGS)"

# Quick self-checking smoke & CSR regression target (compiles once, verifies PASS on each run)
smoke: compile
	$(MAKE) run SEQ=uart_smoke_vseq RUN_NAME=uart_smoke_vseq SEED=1
	grep -q "TEST PASSED" $(RUN_BASE_DIR)1.run_uart_smoke_vseq/vcs.log
	$(MAKE) run SEQ=uart_axi_toggle_vseq RUN_NAME=uart_axi_toggle_vseq SEED=1
	grep -q "TEST PASSED" $(RUN_BASE_DIR)1.run_uart_axi_toggle_vseq/vcs.log
	$(MAKE) run SEQ=uart_sec_cm_vseq RUN_NAME=uart_sec_cm_vseq SEED=1
	grep -q "TEST PASSED" $(RUN_BASE_DIR)1.run_uart_sec_cm_vseq/vcs.log
	$(MAKE) run SEQ=uart_common_vseq RUN_NAME=uart_csr_hw_reset SEED=1 EXTRA_ARGS="+en_scb=0 +csr_hw_reset"
	grep -q "TEST PASSED" $(RUN_BASE_DIR)1.run_uart_csr_hw_reset/vcs.log
	$(MAKE) run SEQ=uart_common_vseq RUN_NAME=uart_csr_rw SEED=1 EXTRA_ARGS="+en_scb=0 +csr_rw"
	grep -q "TEST PASSED" $(RUN_BASE_DIR)1.run_uart_csr_rw/vcs.log
	$(MAKE) run SEQ=uart_common_vseq RUN_NAME=uart_csr_mem_rw_with_rand_reset SEED=1 EXTRA_ARGS="+en_scb=0 +run_csr_mem_rw_with_rand_reset +test_timeout_ns=10000000000"
	grep -q "TEST PASSED" $(RUN_BASE_DIR)1.run_uart_csr_mem_rw_with_rand_reset/vcs.log
	$(MAKE) run SEQ=uart_common_vseq RUN_NAME=uart_csr_mem_rw_with_rand_reset SEED=2 EXTRA_ARGS="+en_scb=0 +run_csr_mem_rw_with_rand_reset +test_timeout_ns=10000000000"
	grep -q "TEST PASSED" $(RUN_BASE_DIR)2.run_uart_csr_mem_rw_with_rand_reset/vcs.log
	$(MAKE) run SEQ=uart_common_vseq RUN_NAME=uart_intr_test SEED=1 EXTRA_ARGS="+run_intr_test"
	grep -q "TEST PASSED" $(RUN_BASE_DIR)1.run_uart_intr_test/vcs.log
	@echo "UART smoke & CSR regression passed!"

verdi:
	@if [ -n "$(LATEST_RUN)" ]; then \
		echo "Opening Verdi for $(LATEST_RUN)..."; \
		verdi -dbdir $(LATEST_RUN)/simv.daidir -ssf $(LATEST_RUN)/dump.fsdb & \
	else \
		echo "No run directory found!"; \
	fi
