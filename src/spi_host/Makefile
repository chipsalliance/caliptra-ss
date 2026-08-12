# Portably find the repository root
export CALIPTRA_SS_ROOT ?= $(shell git rev-parse --show-toplevel)
export CALIPTRA_ROOT ?= $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl

# Check if VCS is in the PATH
ifeq ($(shell which vcs 2>/dev/null),)
$(error "VCS not found in PATH. Please source the environment first (e.g., source /workspace/mnt/env/sim/vcs.env)")
endif

# Allow tool override
TEST= spi_host_base_test
SEQ = spi_host_smoke_vseq

RUN_DIR := run_$(SEQ)_$(shell date +'%Y%m%d-%H%M%S')
# Executables and Filelists
VCS = vcs
SIMV = ./simv
FLIST = $(CALIPTRA_SS_ROOT)/src/spi_host/config/spi_host_tb_flat.vf

ifneq ($(filter 1, $(WAVES) $(DUMP) $(DEBUG)),)
 VCS_DEBUG = -debug_access+all -kdb +memcbk +define+VCS_DEBUG
# FSDB_DUMP = +fsdb+mda +fsdb+mda_depth=0 +fsdb+struct
endif

# Standard Flags
VCS_FLAGS = -sverilog -full64 -ntb_opts uvm-1.2 -timescale=1ns/1ps -notice $(VCS_DEBUG) \
            +define+UVM +define+UVM_NO_DEPRECATED +define+UVM_REGEX_NO_DPI \
            +define+UVM_REG_ADDR_WIDTH=32 +define+UVM_REG_DATA_WIDTH=32 +define+SIMULATION +define+INC_ASSERT -debug_access+all\
            -top tb -f $(FLIST) -o $(SIMV)
LATEST_RUN = $(shell ls -td run_* 2>/dev/null | head -n 1)

verdi:
	@if [ -n "$(LATEST_RUN)" ]; then 		echo "Opening Verdi for $(LATEST_RUN)..."; 		verdi -dbdir $(LATEST_RUN)/simv.daidir -ssf $(LATEST_RUN)/dump.fsdb & 	else 		echo "No run directory found!"; 	fi

RUN_FLAGS = +UVM_TESTNAME=${TEST} +UVM_TEST_SEQ=${SEQ}

.PHONY: all help compile run sim clean

help:
	@echo "SPI Host UVM Testbench Makefile"
	@echo "Usage:"
	@echo "  make compile  - Compiles the design and generates $(SIMV)"
	@echo "  make run      - Runs the simulation using existing $(SIMV)"
	@echo "  make sim      - Compiles AND runs the simulation"
	@echo "  make clean    - Removes generated files and logs"

compile:
	mkdir -p $(RUN_DIR)
	cd $(RUN_DIR) && \
	$(VCS) $(VCS_FLAGS) -l compile.log

run:
	mkdir -p $(RUN_DIR)
	cd $(RUN_DIR) && \
	$(SIMV) -l sim.log $(RUN_FLAGS)

sim:
	mkdir -p $(RUN_DIR)
	cd $(RUN_DIR) && \
	$(VCS) $(VCS_DEBUG) $(VCS_FLAGS) -l sim.log -R $(RUN_FLAGS) $(FSDB_DUMP)   

clean:
	rm -rf simv* csrc *.log ucli.key vc_hdrs.h
