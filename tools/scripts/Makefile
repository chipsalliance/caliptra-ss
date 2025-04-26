# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

PLAYBOOK_RANDOM_SEED ?= $(shell date +%s)
BUILD_CFLAGS ?=
TEST_CFLAGS = -g -O3 -DMY_RANDOM_SEED=$(PLAYBOOK_RANDOM_SEED) $(BUILD_CFLAGS)
VERILATOR = verilator
GCC_PREFIX = riscv64-unknown-elf
BUILD_DIR = $(CURDIR)

ifndef CALIPTRA_SS_CLK_FREQ
# FIXME : Support 170MHz, 200MHz, 400MHz
#CALIPTRA_SS_CLK_FREQ := $(word $(shell echo $$((RANDOM % 3 + 1))), 170 200 400)
CALIPTRA_SS_CLK_FREQ := $(word $(shell echo $$((RANDOM % 3 + 1))), 400 400 400)
endif

# Ensure that RISC-V toolchain is installed
ifeq ($(shell which $(GCC_PREFIX)-gcc 2> /dev/null),)
$(error RISC-V toolchain not found, please refer to https://github.com/chipsalliance/caliptra-rtl?tab=readme-ov-file#riscv-toolchain-installation for more details)
endif

rv_gcc_version = $(strip $(shell $(GCC_PREFIX)-gcc --version | head -1 | sed "s/$(GCC_PREFIX)-gcc (.*) //"))
$(info rv_gcc_version is $(rv_gcc_version))

ifeq "12.2.0" "$(word 1, $(sort 12.2.0 $(rv_gcc_version)))"
# ABI = -mabi=ilp32 -march=rv32imc_zicsr_zifencei_zba_zbb_zbc_zbs
ABI = -mabi=ilp32 -march=rv32imc_zicsr_zifencei --verbose
else
ABI = -mabi=ilp32 -march=rv32imc
endif

# Define test name
TESTNAME ?= mcu_hello_world
CALIPTRA_TESTNAME ?= cptra_hello_world
TEST_DIR ?= $(CALIPTRA_SS_ROOT)/src/integration/test_suites/$(TESTNAME)
HEX_DIR = $(CALIPTRA_SS_ROOT)/src/integration/test_suites/hex
INCLUDES_DIR = $(CALIPTRA_SS_ROOT)/src/integration/test_suites/includes
RTL_DIR = $(CALIPTRA_SS_ROOT)/src/integration/rtl
TBDIR ?= $(CALIPTRA_SS_ROOT)/src/integration/testbench
RISCV_HW_IF_DIR = $(CALIPTRA_SS_ROOT)/src/integration/test_suites/libs/riscv_hw_if
ISR_DIR    = $(CALIPTRA_SS_ROOT)/src/integration/test_suites/libs/mcu_isr
PRINTF_DIR = $(CALIPTRA_SS_ROOT)/src/integration/test_suites/libs/printf
LIBS_DIR = $(CALIPTRA_SS_ROOT)/src/integration/test_suites/libs
CSS_MCU0_DEFINES_DIR = $(CALIPTRA_SS_ROOT)/src/riscv_core/veer_el2/rtl/defines


DUT ?= caliptra_ss_top_tb

CALIPTRA_DIR = $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/src/integration/test_suites
SOC_IFC_DIR = $(CALIPTRA_DIR)/libs/soc_ifc
CALIPTRA_ROOT = $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl
CALIPTRA_RTL = $(CALIPTRA_ROOT)/src/integration/rtl

# Determine test directory
#ifneq (,$(wildcard $(TBDIR)/tests/$(TEST)))
#  TEST_DIR = $(TBDIR)/tests/$(TEST)
#endif

# Libraries providing functionality for each peripheral component in Caliptra Subsystem
COMP_LIB_NAMES := caliptra_ss_lib \
		  mci \
		  fuse_ctrl \
		  lc_ctrl \
		  wdt
COMP_LIBS := $(foreach name, $(COMP_LIB_NAMES), $(LIBS_DIR)/$(name))
HEADER_FILES := $(RTL_DIR)/soc_address_map.h \
		$(RTL_DIR)/fuse_ctrl_address_map.h \
		$(RTL_DIR)/caliptra_ss_lc_ctrl_address_map.h \
		$(INCLUDES_DIR)/caliptra_ss_defines.h \
		$(RISCV_HW_IF_DIR)/riscv_hw_if.h \
		$(RISCV_HW_IF_DIR)/riscv-csr.h \
		$(RISCV_HW_IF_DIR)/veer-csr.h \
		$(wildcard $(TEST_DIR)/*.h) \
		$(SOC_IFC_DIR)/soc_ifc.h \
		$(PRINTF_DIR)/printf.h \
		$(CSS_MCU0_DEFINES_DIR)/css_mcu0_defines.h \
		$(BUILD_DIR)/caliptra_ss_clk_freq.h \
		$(foreach comp_lib, $(COMP_LIBS), $(wildcard $(comp_lib)/*.h))

TEST_GEN_FILES := $(CALIPTRA_SS_ROOT)/src/fuse_ctrl/data/otp-img.2048.vmem \
	          $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/src/ecc/tb/ecc_secp384r1.exe \
	          $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/src/doe/tb/doe_test_gen.py \
	          $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/src/sha256/tb/sha256_wntz_test_gen.py \
                  $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/src/integration/tb/vectors/SHA*.rsp \
	          $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/submodules/adams-bridge/src/mldsa_top/uvmf/Dilithium_ref/dilithium/ref/test/test_dilithium5 \
	          $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/submodules/adams-bridge/src/mldsa_top/uvmf/Dilithium_ref/dilithium/ref/test/test_dilithium5_debug \
	          $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/src/mldsa/tb/smoke_test_mldsa_vector.hex

# Separate OFILE variable since this is not used to build remote images
# (i.e. FMC or RunTime)
ifeq (0,$(shell test -e $(TEST_DIR)/$(TESTNAME).c && echo $$?))
	OFILE_CRT := mcu_crt0.o
endif
OFILES += $(TESTNAME).o
# Assume all C tests will import our printf and ISR libs, but assembly
# tests will not
ifeq (0,$(shell test -e $(TEST_DIR)/$(TESTNAME).c && echo $$?))
	OFILES += printf.o
endif
ifeq (0,$(shell test -e $(TEST_DIR)/$(TESTNAME).c && echo $$?))
	OFILES += $(foreach comp_lib_name, $(COMP_LIB_NAMES), $(comp_lib_name).o)
endif

# Only build the mcu_isr lib (which consumes a large block of DCCM) if it is
# included by the test code.
ifeq (0,$(shell grep -e '\#include "mcu_isr.h"' $(TEST_DIR)/$(TESTNAME).c > /dev/null && echo $$?))
	OFILES += mcu_isr.o
# Tests might have a local variant of mcu_isr header
# If not, use the default
ifeq (0,$(shell test -e $(TEST_DIR)/mcu_isr.h && echo $$?))
	HEADER_FILES += $(TEST_DIR)/mcu_isr.h
else
	HEADER_FILES += $(ISR_DIR)/mcu_isr.h
endif
HEADER_FILES += $(ISR_DIR)/riscv-interrupts.h
endif

# Verilator trace format
VERILATOR_TRACE=vcd

ifdef debug
 DEBUG_PLUS = +dumpon
 IRUN_DEBUG = -access +rc
 IRUN_DEBUG_RUN = -input $(RV_ROOT)/testbench/input.tcl
 VCS_DEBUG = -debug_access
 ifeq ($(VERILATOR_TRACE), vcd)
  VERILATOR_DEBUG = --trace --trace-structs
 else ifeq ($(VERILATOR_TRACE), fst)
  VERILATOR_DEBUG = --trace-fst --trace-structs --trace-threads 2
 else
  $(error Unsupported Verilator trace format '$(VERILATOR_TRACE)')
 endif
 RIVIERA_DEBUG = +access +r
endif

# RK
# provide specific link file
ifeq (,$(wildcard $(TEST_DIR)/$(TESTNAME).ld))
	LINK = $(RISCV_HW_IF_DIR)/link.ld
else
	LINK = $(TEST_DIR)/$(TESTNAME).ld
endif

VPATH = $(TEST_DIR) $(BUILD_DIR) $(TBDIR) $(RISCV_HW_IF_DIR) $(SOC_IFC_DIR) $(PRINTF_DIR) $(ISR_DIR) $(COMP_LIBS)

# Use eval to expand env variables in the .vf file
$(eval TBFILES = $(shell cat $(TBDIR)/../config/$(DUT).vf | grep -v '+incdir+'))

#defines  = $(BUILD_DIR)/common_defines.vh
#defines += $(RV_ROOT)/design/include/el2_def.sv
#defines += $(BUILD_DIR)/el2_pdef.vh
includes = -I$(BUILD_DIR)
#
#         .--------------------------------------------------------------------------------.
#         | Verilator does not support unpacked structs/unions - waive this warning so     |
#         | that unpacked structs are treated as packed. This should only impact files     |
#         | generated from RDL register files, which use unpacked structs liberally.       |
#         '-----------------------------------------------------------------------------+--'
#                                                                                       |
#         .---------------------------------------------------------------------.       |
#         | This is flagged for every generated SystemVerilog file defining a   |       |
#         | register block. The field_storage signal is the target of the       |       |
#         | warning, indicating multiple drivers/different clocking.            |       |
#         '----------------------------------------------------------------+----'       |
#                                                                          |            |
#         .------------------------------------------------------.         |            |
#         | PeakRDL implements the default incrsaturate behavior |         |            |
#         | for counter registers by performing a > comparison   |         |            |
#         | with an all-ones value (i.e. cnt > 32'hFFFFFFFF)     |         |            |
#         | which, by definition, can never be true. Verilator   |         |            |
#         | warns that this will compile to a constant 0.        |         |            |
#         '------------------------------------------------+-----'         |            |
#                                                          |               |            |
#         .--------------------------------------------.   |               |            |
#         | Vectors that are little bit-endian are not |   |               |            |
#         | supported by Verilator, according to a     |   |               |            |
#         | warning that is thrown. This is supposedly |   |               |            |
#         | resolved as of version 3.720, according    |   |               |            |
#         | to the release notes.                      |   |               |            |
#         '-----------------------------------+--------'   |               |            |
#                                             |            |               |            |
#         .------------------------------.    |            |               |            |
#         | Inherited from ChipsAlliance |    |            |               |            |
#         | VeeR repository provided     |    |            |               |            |
#         | Makefile                     |    |            |               |            |
#         '-----+------------+-----------'    |            |               |            |
#               |            |                |            |               |            |
#               v            v                v            v               v            v
suppress = -Wno-WIDTH -Wno-UNOPTFLAT -Wno-LITENDIAN -Wno-CMPCONST -Wno-MULTIDRIVEN -Wno-UNPACKED

# CFLAGS for verilator generated Makefiles. Without -std=c++17 it
# complains for `auto` variables
CFLAGS += -std=c++17
#CFLAGS += -std=c11

# Optimization for better performance; alternative is nothing for
# slower runtime (faster compiles) -O2 for faster runtime (slower
# compiles), or -O for balance.
VERILATOR_MAKE_FLAGS = OPT_FAST="-Os"

# Testbench DPI sources
TB_DPI_SRCS = jtagdpi/jtagdpi.c \
              tcp_server/tcp_server.c

TB_DPI_INCS := $(addprefix -I$(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/src/integration/test_suites/libs/,$(dir $(TB_DPI_SRCS)))
TB_DPI_SRCS := $(addprefix $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/src/integration/test_suites/libs/,$(TB_DPI_SRCS))

# Testbench sources
TB_VERILATOR_SRCS = $(TBDIR)/test_$(DUT).cpp $(TB_DPI_SRCS)

# Testbench defs
TB_DEFS = +define+CALIPTRA_INTERNAL_QSPI+CALIPTRA_INTERNAL_TRNG+CALIPTRA_INTERNAL_UART

# By default debugging (JTAG) is locked in Caliptra. Add "DEBUG_UNLOCKED=1" to
# enable it.
ifdef DEBUG_UNLOCKED
    TB_DEFS += +define+CALIPTRA_DEBUG_UNLOCKED
endif

# To enforce holding the RISC-V core in reset add "FORCE_CPU_RESET=1".
ifdef FORCE_CPU_RESET
    TB_DEFS += +define+CALIPTRA_FORCE_CPU_RESET
endif

# Run time arguments from command line
VERILATOR_RUN_ARGS ?= ""

# Add testbench lib include paths
CFLAGS += $(TB_DPI_INCS)

############# VCS Compile options #############
VCS_COMP_OPTS += -debug_access+all
VCS_COMP_OPTS += +define+CLP_ASSERT_ON
VCS_COMP_OPTS += +define+AVERY_ASSERT_ON
VCS_COMP_OPTS += +define+AVERY_MONITOR_ON
# Used in caliptra_top_sva to find signals
VCS_COMP_OPTS += +define+CPTRA_TB_TOP_NAME=$(DUT)
VCS_COMP_OPTS += +define+CPTRA_TOP_PATH=$(DUT).caliptra_ss_dut.caliptra_top_dut
VCS_COMP_OPTS += +define+CALIPTRA_MODE_SUBSYSTEM
VCS_COMP_OPTS += +define+MCU_RV_BUILD_AXI4
VCS_COMP_OPTS += +define+MCU_RV_OPENSOURCE
VCS_COMP_OPTS += +define+AVERY_VCS
VCS_COMP_OPTS += +define+AVERY_CLOCK=5
VCS_COMP_OPTS += +define+FOUR_OUTSTANDING
VCS_COMP_OPTS += +define+AVERY_AXI_INTERCONNECT
VCS_COMP_OPTS += +define+AAXI_MAX_DATA_WIDTH=64
VCS_COMP_OPTS += +define+AAXI_MAX_ADDR_WIDTH=64
VCS_COMP_OPTS += +define+AAXI_MAX_ID_WIDTH=5
VCS_COMP_OPTS += +define+AAXI_MAX_ARUSER_WIDTH=32
VCS_COMP_OPTS += +define+AAXI_MAX_AWUSER_WIDTH=32
VCS_COMP_OPTS += +define+CALIPTRA_INTERNAL_UART
VCS_COMP_OPTS += -noinherit_timescale=1ns/1ps
VCS_COMP_OPTS += +define+AAXI_INTC_MASTER_CNT=5
VCS_COMP_OPTS += +define+AAXI_INTC_SLAVE_CNT=8
VCS_COMP_OPTS += +define+AI3C_LANE_NUM=1
VCS_COMP_OPTS += +define+DIGITAL_IO_I3C=1
#VCS_COMP_OPTS += +define+AI3C_SKIP_DAA=1
VCS_COMP_OPTS += +define+AVERY_SV_TEST_CASE=1
VCS_COMP_OPTS += +define+AI3C_TEST_CASE=$(TBDIR)/sv_tests/ai3c/ai3c_test_includes.svh
VCS_COMP_OPTS += $(AVERY_PLI)/lib.linux/libtb_vcs64.a
VCS_COMP_OPTS += -P $(AVERY_PLI)/tb_vcs64.tab
#FIXME : remve this Note suppression
VCS_COMP_OPTS += -suppress=SV-LCM-PPWI
############# VCS Elab options #############
#FIXME implicit-wire-no-fanin and port-connection-width-mismatch warnings from i3c_core
VCS_ELAB_OPTS += +warn=noIWNF
VCS_ELAB_OPTS += +warn=noPCWM-W
VCS_ELAB_OPTS += +warn=noTFIPC,noMDVMO
VCS_ELAB_OPTS += $(AVERY_PLI)/lib.linux/libtb_vcs64.a
VCS_ELAB_OPTS += -P $(AVERY_PLI)/tb_vcs64.tab
#FIXME unique case violations in i3c_core
VCS_ELAB_OPTS += -ignore unique_checks
############# VCS Simulation options #############
VCS_SIM_OPTS  += +vpi -lpthread
VCS_SIM_OPTS  += +CLP_BUS_LOGS=1

# Targets
all: clean verilator

clean:
	rm -rf *.log *.s *.hex *.dis *.size *.tbl irun* vcs* simv* .map *.map snapshots \
	verilator* *.exe obj* *.o ucli.key vc_hdrs.h csrc *.csv work \
	dataset.asdb  library.cfg vsimsa.cfg  riviera-build wave.asdb sim.vcd \
	*.h

clean_fw:
	rm -rf *.o *.h

############ Model Builds ###############################

#verilator-build: $(TBFILES) $(INCLUDES_DIR)/defines.h $(TB_VERILATOR_SRCS)
verilator-build: $(INCLUDES_DIR)/defines.h $(TB_VERILATOR_SRCS)
	$(VERILATOR) $(TB_VERILATOR_SRCS) --cc -CFLAGS "$(CFLAGS)" \
	  +libext+.v+.sv +define+RV_OPENSOURCE \
	  --timescale 1ns/1ps \
		--timing \
	  $(includes) \
	  $(suppress) \
	  -f $(TBDIR)/../config/$(DUT).vf --top-module $(DUT) \
	  -f $(TBDIR)/../config/$(DUT).vlt \
	  -exe test_$(DUT).cpp --autoflush $(VERILATOR_DEBUG) \
	  $(TB_DEFS)
	$(MAKE) -j`nproc` -e -C obj_dir/ -f V$(DUT).mk $(VERILATOR_MAKE_FLAGS) VM_PARALLEL_BUILDS=1
	touch verilator-build

vcs-build: $(TBFILES) $(TB_DPI_SRCS)
	vlogan -sverilog -full64 -assert svaext -kdb -incr_vlogan +lint=IA_CHECKFAIL \
	  $(VCS_COMP_OPTS) \
	  -l vcs_compile.log \
	  -f $(TBDIR)/../config/$(DUT).vf
	vcs -full64 -kdb -lca -j8 +vcs+lic+wait -partcomp -fastpartcomp=j8 \
	  $(VCS_ELAB_OPTS) \
	  -l vcs_elab.log \
	  -assert enable_hier $(DUT) -o simv.$(DUT) +dpi -cflags "$(TB_DPI_INCS)" $(TB_DPI_SRCS)

############ TEST Simulation ###############################

verilator: mcu_program.hex verilator-build
	./obj_dir/V$(DUT) $(VERILATOR_RUN_ARGS)

vcs: cptra_program.hex mcu_program.hex vcs-build
	cp $(TEST_GEN_FILES) $(BUILD_DIR)
	./simv.$(DUT) \
	  $(VCS_SIM_OPTS) \
	  -l vcs_sim.log

############ Caliptra TEST build ######################
ifneq (,$(wildcard $(CALIPTRA_ROOT)/src/integration/test_suites/$(CALIPTRA_TESTNAME)))
cptra_program.hex:
	make -f $(CALIPTRA_ROOT)/tools/scripts/Makefile CALIPTRA_INTERNAL_TRNG=0 TESTNAME=$(CALIPTRA_TESTNAME) program.hex
else ifneq (,$(wildcard $(CALIPTRA_SS_ROOT)/src/integration/test_suites/$(CALIPTRA_TESTNAME)))
cptra_program.hex:
	make -f $(CALIPTRA_ROOT)/tools/scripts/Makefile CALIPTRA_INTERNAL_TRNG=0 TEST_DIR=$(CALIPTRA_SS_ROOT)/src/integration/test_suites/$(CALIPTRA_TESTNAME) TESTNAME=$(CALIPTRA_TESTNAME) program.hex
else
cptra_program.hex:
	make -f $(CALIPTRA_ROOT)/tools/scripts/Makefile CALIPTRA_INTERNAL_TRNG=0 TEST_DIR=$(TEST_DIR) TESTNAME=$(CALIPTRA_TESTNAME) program.hex
endif

############ MCU TEST build ###############################

ifeq ($(shell which $(GCC_PREFIX)-gcc 2> /dev/null),)
mcu_program.hex: $(BUILD_DIR)/defines.h
	@echo " !!! No $(GCC_PREFIX)-gcc in path, using canned hex files !!"
	cp $(HEX_DIR)/$(TESTNAME).hex mcu_program.hex
else ifneq (,$(wildcard $(TEST_DIR)/$(TESTNAME).makefile))
mcu_program.hex:
	@echo Building $(TESTNAME) via $(TEST_DIR)/$(TESTNAME).makefile
	$(MAKE) -f $(TEST_DIR)/$(TESTNAME).makefile
else ifneq (,$(wildcard $(TEST_DIR)/$(TESTNAME)))
# Build mcu_program.hex from RUST executable
# TODO update this if/when we have pre-built binaries to test
mcu_program.hex:
	@echo "Building mcu_program.hex from $(TESTNAME) using rules for pre-compiled RUST executables"
	-$(GCC_PREFIX)-objcopy -O verilog -R .data -R .rodata -R .bss -R .sbss -R .iccm -R .dccm -R .eh_frame --pad-to 0xC000 --gap-fill 0xFF --no-change-warnings $(TEST_DIR)/$(TESTNAME) mcu_program.hex
	-$(GCC_PREFIX)-objcopy -O verilog -j .data -j .rodata -j .bss -j .sbss -j .dccm \
			      --change-section-lma       .data-0x80000000 \
			      --change-section-lma     .rodata-0x80000000 \
			      --change-section-lma        .bss-0x80000000 \
			      --change-section-lma       .sbss-0x80000000 \
			      --change-section-lma       .dccm-0x80000000 \
			      --pad-to 0x20000 \
			      --no-change-warnings \
			      $(TEST_DIR)/$(TESTNAME) mcu_dccm.hex
	$(GCC_PREFIX)-objdump -S  $(TEST_DIR)/$(TESTNAME) > $(TESTNAME).dis
	$(GCC_PREFIX)-size        $(TEST_DIR)/$(TESTNAME) | tee $(TESTNAME).size

else
mcu_program.hex: $(OFILE_CRT) $(OFILES) $(LINK)
	@echo Building $(TESTNAME)
	$(GCC_PREFIX)-gcc $(ABI) -Wl,-Map=$(TESTNAME).map -lgcc -T$(LINK) -o $(TESTNAME).exe $(OFILE_CRT) $(OFILES) -nostartfiles  $(TEST_LIBS)
	#-$(GCC_PREFIX)-objcopy --dump-section .dccm=dccm_section.bin $(TESTNAME).exe
	#-$(GCC_PREFIX)-objcopy -O verilog -I binary dccm_section.bin mcu_dccm.hex
	-$(GCC_PREFIX)-objcopy -O verilog -j .dccm -j .data -j .sdata -j .bss -j .sbss \
			      --change-section-lma       .dccm-0x50000000 \
			      --change-section-lma       .data-0x50000000 \
			      --change-section-lma      .sdata-0x50000000 \
			      --change-section-lma        .bss-0x50000000 \
			      --change-section-lma       .sbss-0x50000000 \
			      --pad-to 0x4000 \
			      --no-change-warnings \
			      $(TESTNAME).exe mcu_dccm.hex
	-$(GCC_PREFIX)-objcopy -O verilog -j .text -j .rodata -j .srodata \
			      --change-section-lma       .text-0x80000000 \
			      --change-section-lma     .rodata-0x80000000 \
			      --change-section-lma    .srodata-0x80000000 \
			      --pad-to 0x40000 \
			      --no-change-warnings $(TESTNAME).exe mcu_program.hex
	-$(GCC_PREFIX)-objcopy -O binary           -R .data.io -R .eh_frame --pad-to 0x40000  --no-change-warnings $(TESTNAME).exe mcu_program.bin
	-$(GCC_PREFIX)-objcopy -O verilog -j .mcu_sram \
			      --change-section-lma .mcu_sram-0x21C00000 \
			      --pad-to 0x80000 \
			      --no-change-warnings $(TESTNAME).exe mcu_lmem.hex
	-$(GCC_PREFIX)-objcopy -O verilog -j .mcu_hitless_sram \
				--change-section-lma .mcu_hitless_sram-0x21C00000 \
				--pad-to 0x80000 \
				--no-change-warnings $(TESTNAME).exe mcu_hitless_lmem.hex			  
	# $(GCC_PREFIX)-objcopy -O verilog -R .text -R .rodata -R .srodata -R .bss -R .sbss -R .data.io -R .eh_frame --pad-to 0x20000 --no-change-warnings $(TESTNAME).exe mcu_lmem.hex
	# $(GCC_PREFIX)-objcopy -O verilog -R .data -R .rodata -R .srodata -R .bss -R .sbss -R .data.io -R .eh_frame --pad-to 0x20000 --no-change-warnings $(TESTNAME).exe mcu_program.hex
	$(GCC_PREFIX)-objdump -S  $(TESTNAME).exe > $(TESTNAME).dis
	$(GCC_PREFIX)-size        $(TESTNAME).exe | tee $(TESTNAME).size
	riscv64-unknown-elf-nm -B -n $(TESTNAME).exe > $(TESTNAME).sym
	@echo Completed building $(TESTNAME)

# $(GCC_PREFIX)-objcopy -O verilog -R .text -R .data.io -R .eh_frame --pad-to 0x20000 --no-change-warnings $(TESTNAME).exe mcu_lmem.hex
# $(GCC_PREFIX)-objcopy -O verilog -j .dccm --change-section-lma .dccm-0x50000000 --no-change-warnings $(TESTNAME).exe mcu_dccm.hex
# cp /home/pure_scratch/caliptra/users/users/pateln/veer_el2_core_ws2/hello_world.dis mcu_hello_world.dis
# cp /home/pure_scratch/caliptra/users/users/pateln/veer_el2_core_ws2/hello_world.sym mcu_hello_world.sym
# cp /home/pure_scratch/caliptra/users/users/pateln/veer_el2_core_ws2/hello_world.exe mcu_hello_world.exe
# cp /home/pure_scratch/caliptra/users/users/pateln/veer_el2_core_ws2/hello_world.map mcu_hello_world.map
# cp /home/pure_scratch/caliptra/users/users/pateln/veer_el2_core_ws2/program.hex program.hex

# $(GCC_PREFIX)-gcc $(ABI) -Wl,-Map=$(TESTNAME).map -lgcc -T$(LINK) -o $(TESTNAME).exe $(OFILE_CRT) $(OFILES) -nostartfiles  $(TEST_LIBS)
# riscv64-unknown-elf-objcopy -O verilog  mcu_hello_world.exe program.hex
# riscv64-unknown-elf-objdump -S  mcu_hello_world.exe > mcu_hello_world.dis
# riscv64-unknown-elf-nm -B -n mcu_hello_world.exe > mcu_hello_world.sym
# -$(GCC_PREFIX)-objcopy -O verilog -R .data_iccm0 -R .data_iccm1 -R .data_iccm2 -R .iccm -R .dccm -R .eh_frame --pad-to 0xC000 --no-change-warnings $(TESTNAME).exe program.hex
# -$(GCC_PREFIX)-objcopy -O verilog -j .data_iccm0 -j .data_iccm1 -j .data_iccm2 -j .dccm \
# 				--change-section-lma .data_iccm0-0x50000000 \
# 				--change-section-lma .data_iccm1-0x50000000 \
# 				--change-section-lma .data_iccm2-0x50000000 \
# 				--change-section-lma       .dccm-0x50000000 \
# 				--pad-to 0x20000 \
# 				--no-change-warnings \
# 				$(TESTNAME).exe dccm.hex
# -$(GCC_PREFIX)-objcopy -O verilog -j .iccm                       --change-section-address .iccm=0 --pad-to 0x20000 --no-change-warnings $(TESTNAME).exe iccm.hex
# -$(GCC_PREFIX)-objcopy -O verilog -j .mailbox --gap-fill 0x0     --change-section-address .mailbox=0 --pad-to 0x20000 --no-change-warnings $(TESTNAME).exe mailbox.hex
# $(GCC_PREFIX)-objdump -S  $(TESTNAME).exe > $(TESTNAME).dis
# $(GCC_PREFIX)-size        $(TESTNAME).exe | tee $(TESTNAME).size

# Cannot build caliptra_{fmc,rt}.hex and program.hex in the same make invocation (TESTNAME will be invalid, and consequently other dependencies like LINK)
# Entire image will be loaded into the mailbox, so it must fit the 128KiB memory
%.hex: $(OFILES) $(LINK)
	@echo Building $(TESTNAME)
	$(GCC_PREFIX)-gcc $(ABI) -Wl,-Map=$(TESTNAME).map -lgcc -T$(LINK) -o $(TESTNAME).exe $(OFILES) -nostartfiles  $(TEST_LIBS)
	-$(GCC_PREFIX)-objcopy -O verilog -R .eh_frame --pad-to 0x20000 --no-change-warnings $(TESTNAME).exe $@
	$(GCC_PREFIX)-objdump -S  $(TESTNAME).exe > $(TESTNAME).dis
	$(GCC_PREFIX)-size        $(TESTNAME).exe | tee $(TESTNAME).size
	@echo Completed building $(TESTNAME)

%.o : %.s $(HEADER_FILES)
	@echo " !!! Executing *.s files !!"
	cp $(filter-out %/caliptra_ss_clk_freq.h, $(HEADER_FILES)) $(BUILD_DIR)
	$(GCC_PREFIX)-cpp -I${BUILD_DIR}  $<  > $*.cpp.s
	$(GCC_PREFIX)-as $(ABI) $*.cpp.s -o $@

%.o : %.c $(HEADER_FILES)
	cp $(filter-out %/caliptra_ss_clk_freq.h, $(HEADER_FILES)) $(BUILD_DIR)
	$(GCC_PREFIX)-gcc $(includes) $(TEST_CFLAGS) -DCOMPILER_FLAGS="\"$(TEST_CFLAGS)\"" $(ABI) -nostdlib -c $< -o $@

$(BUILD_DIR)/caliptra_ss_clk_freq.h: $(CALIPTRA_SS_ROOT)/tools/scripts/gen_clk_freq_file.sh
	$(CALIPTRA_SS_ROOT)/tools/scripts/gen_clk_freq_file.sh $(BUILD_DIR) $(CALIPTRA_SS_CLK_FREQ)

endif

help:
	@echo Make sure the environment variable RV_ROOT is set.
	@echo Possible targets: verilator vcs irun vlog riviera help clean all verilator-build irun-build vcs-build riviera-build program.hex

.PHONY: help clean clean_fw verilator vcs irun vlog riviera