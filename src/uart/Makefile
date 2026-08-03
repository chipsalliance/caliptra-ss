# SPDX-License-Identifier: Apache-2.0

SHELL   = bash
PYTHON ?= python3

# Allow tool override
TEST = uart_base_test
SEQ = uart_smoke_vseq

# Check for CALIPTRA_SS_ROOT
ifeq (,$(wildcard ${CALIPTRA_SS_ROOT}/src/uart))
$(error env var CALIPTRA_SS_ROOT does not point to a valid dir! Exiting!)
endif


clean: 
	rm -rf simv* *.log csrc ucli.key vc_hdrs.h

RUN_DIR := run_$(SEQ)_$(shell date +'%Y%m%d-%H%M%S')

ifneq ($(filter 1, $(WAVES) $(DUMP) $(DEBUG)),)
 VCS_DEBUG = -debug_access+all -kdb +memcbk +define+VCS_DEBUG
endif

LATEST_RUN = $(shell ls -td run_* 2>/dev/null | head -n 1)

verdi:
	@if [ -n "$(LATEST_RUN)" ]; then 		echo "Opening Verdi for $(LATEST_RUN)..."; 		verdi -dbdir $(LATEST_RUN)/simv.daidir -ssf $(LATEST_RUN)/dump.fsdb & 	else 		echo "No run directory found!"; 	fi

vcs:
	mkdir -p $(RUN_DIR)
	cd $(RUN_DIR) && \
	vcs $(VCS_DEBUG) -sverilog -full64 -ntb_opts uvm-1.2 \
		+define+SIMULATION +define+INC_ASSERT +define+DISABLE_ALERT_SVA \
		+define+UVM +define+UVM_NO_DEPRECATED +define+UVM_REGEX_NO_DPI \
		+define+UVM_REG_ADDR_WIDTH=32 +define+UVM_REG_DATA_WIDTH=32 \
		-timescale=1ns/1ps -notice \
		-kdb -debug_access+all  \
		-top tb -f ${CALIPTRA_SS_ROOT}/src/uart/config/uart_tb_flat.vf \
		-o simv -l build.log && ./simv +fsdb+mda +fsdb+mda_depth=0 +fsdb+struct \
		+UVM_TESTNAME=${TEST} +UVM_TEST_SEQ=${SEQ}
