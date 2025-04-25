_*SPDX-License-Identifier: Apache-2.0<BR>
<BR>
<BR>
Licensed under the Apache License, Version 2.0 (the "License");<BR>
you may not use this file except in compliance with the License.<BR>
You may obtain a copy of the License at<BR>
<BR>
http://www.apache.org/licenses/LICENSE-2.0 <BR>
<BR>
Unless required by applicable law or agreed to in writing, software<BR>
distributed under the License is distributed on an "AS IS" BASIS,<BR>
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.<BR>
See the License for the specific language governing permissions and<BR>
limitations under the License.*_<BR>

# Caliptra Subsystem Overview
_*Last Update: 2025/04/24*_

HW Design Collateral for Caliptra Subsystem, which comprises Caliptra RoT IP and additional infrastructure to support manufacturer custom controls.

:warning:**$${\textsf{\color{red}DISCLAIMER:\ This\ repository\ is\ under\ active\ development\ and\ has\ no\ official\ release.}}$$**<br>
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;**$${\textsf{\color{red}Functionality\ or\ quality\ is\ not\ guaranteed.}}$$**<br>
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;**$${\textsf{\color{red}Do\ not\ integrate\ this\ into\ a\ production\ design!}}$$**<br>

## Project Links

[caliptra-ss](https://github.com/chipsalliance/caliptra-ss)

## **Tools Used** ##

OS:
 - Build instructions assume a Linux environment

Simulation:
 - Synopsys VCS with Verdi
   - `Version U-2023.03-SP1-1_Full64`
 - Mentor Graphics AVERY
   - `avery/2025.1` AXI interconnect and I3C VIP
 - ARM AXI Protocol Checker
   - `BP063-BU-01000-r0p1-00rel0` Axi4PC.sv may be acquired from the ARM website
 - UVM installation
   - `Version 1.1d`

GCC:
 - RISCV Toolchain for generating memory initialization files
   - `Version 2023.04.29`
   - `riscv64-unknown-elf-gcc (g) 12.2.0`
 - G++ Used to compile Verilator objects and test firmware
   - `g++ (GCC) 11.2.0`

Other:
 - Playbook (Microsoft Internal workflow management tool)

### **RISCV Toolchain installation** ###
There is significant configurability when installing the RISCV toolchain.
These instructions may be used to create a RISCV installation that will be compatible
with the provided Makefile for compiling test C programs.

1. Install from this repository:
    - https://github.com/riscv-collab/riscv-gnu-toolchain
    - Follow the included README in that repository for installation instructions
2. The most recently tested toolchain build that was confirmed to work was 2023-04-29
    - https://github.com/riscv-collab/riscv-gnu-toolchain/releases/tag/2023.04.29
3. A compatible tool installation requires newlib cross-compiler, multilib support, and the zicsr/zifencei extensions. Use this configure command:
    - `./configure --enable-multilib --prefix=/path/to/tools/riscv-gnu/2023.04.29 --with-multilib-generator="rv32imc-ilp32--a*zicsr*zifencei"`
4. Use `make` instead of `make linux` to install the tool (using newlib option)

## **ENVIRONMENT VARIABLES** ##
Required for simulation:<BR>
`CALIPTRA_WORKSPACE`: Defines the absolute path to the directory where the simulation "scratch" output directory will be created. Recommended to define as the absolute path to the directory that contains a subdirectory "chipsalliance" which, in turn, contains the Project repository root (called "caliptra-ss")<BR>
`CALIPTRA_SS_ROOT`: Defines the absolute path to the Project repository root (called "caliptra-ss"). Recommended to define as `${CALIPTRA_WORKSPACE}/chipsalliance/caliptra-ss`.<BR>
`CALIPTRA_ROOT`: Defines the absolute path to the Caliptra submodule root. Must be defined as `${CALIPTRA_SS_ROOT}/third_party/caliptra-rtl`.<BR>
`ADAMSBRIDGE_ROOT`: Defines the absolute path to the Adams-Bridge submodule root. Must be defined as `${CALIPTRA_ROOT}/submodules/adams-bridge`.<BR>
`CALIPTRA_AXI4PC_DIR`: Path to the directory that contains the ARM AXI4 Protocol Checker file. This file must be acquired from the Arm website by integrators, as it contains copyrighted materials.<BR>
`AVERY_HOME`: Installation root for Avery VIP<BR>
`AVERY_PLI`: Directory within AVERY\_HOME that contains avery\_pli<BR>
`AVERY_SIM`: Directory within AVERY\_HOME that contains avery\_sim<BR>
`AVERY_AXI`: Directory within AVERY\_HOME that contains axixactor<BR>
`AVERY_I3C`: Directory within AVERY\_HOME that contains i3cxactor<BR>

Required for Firmware (i.e. Test suites) makefile:<BR>
  `TESTNAME`: Contains the name of one of the tests listed inside the `$CALIPTRA_SS_ROOT/src/integration/test_suites` folder; used for simulations with `caliptra_ss_top_tb` tests<BR>
  `CALIPTRA_TESTNAME`: Identifies which firmware test will be compiled and executed on the Caliptra Core RV processor as part of the Subsystem test. This may indicate the name of a directory inside `$CALIPTRA_ROOT/src/integration/test_suites`, or it may indicate the name of a test firmware file contained inside the caliptra-ss repository for execution on Caliptra core. In this case, the file must be:
  * Named with a `cptra` prefix, to uniquely identify it from MCU firmware test files, and EITHER
  * Located in the same directory as the MCU test firmware, i.e. `$CALIPTRA_SS_ROOT/src/integration/test_suites/$TESTNAME` OR
  * Located in the the test\_suites folder in a directory with the same name as the test file, i.e. `$CALIPTRA_SS_ROOT/src/integration/test_suites/$CALIPTRA_TESTNAME`

## **Repository Overview** ##
```
├── config
│   └── compilespecs.yml
├── docs
│   ├── Caliptra 2.0 Subsystem Specification 1.pdf
│   ├── CaliptraSSHardwareSpecification.md
│   ├── CaliptraSSIntegrationSpecification.md
│   └── images
├── LICENSE
├── README.md
├── Release_Notes.md
├── SECURITY.md
├── src
│   ├── ast
│   ├── axi2tlul
│   ├── axi_mem
│   ├── dmi
│   ├── fuse_ctrl
│   ├── i3c_core
│   ├── integration
│   ├── lc_ctrl
│   ├── libs
│   ├── mci
│   ├── mcu
│   ├── pwrmgr
│   ├── riscv_core
│   └── tlul
├── third_party
│   ├── caliptra-rtl
│   ├── cocotbext-i3c
│   └── i3c-core
└── tools
    └── scripts
```

## **Verilog File Lists** ##
VF files provide absolute filepaths (prefixed by the `CALIPTRA_SS_ROOT` environment variable) to each compile target for the associated component.<BR>
The "Integration" sub-component contains the top-level fileset for Caliptra Subsystem. `src/integration/config/compile.yml` defines the required filesets and sub-component dependencies for this build target. All of the files/dependencies for compiling the top-level testbench are explicitly listed in `src/integration/config/caliptra_ss_top_tb.vf`. Users may compile the entire design using only this VF filelist.<BR>
Verilog file lists are generated via VCS and included in the config directory for each unit. File lists define the compilation sources (including all dependencies) required to build and simulate a given module or testbench, and should be used by integrators for simulation, lint, and synthesis. Compilation using the provided Verilog file lists requires all [environment variables](#environment-variables) to be defined.

Important: Users must download the [ARM AXI4 Protocol Checker](https://developer.arm.com/downloads/view/BP063) from ARM, as it is a dependency
for the Avery AXI VIP. These files contain proprietary materials and therefore are not included in the
caliptra-ss GitHub repository.

## **Simulation Flow** ##

### Caliptra SS Top VCS Steps: ###
1. Setup tools, add to PATH (ensure RISC-V toolchain is also available)
1. Define all environment variables above
    - For the initial test run after downloading repository, `mcu_hello_world` is recommended for TESTNAME
    - See [Regression Tests](#Regression-Tests) for information about available tests
1. Create a run folder for build outputs (and cd to it)
1. Either use the provided Makefile or execute each of the following steps manually to run VCS simulations
1. Makefile usage:
    - Example command:
        `make -C <path/to/run/folder> -f ${CALIPTRA_SS_ROOT}/tools/scripts/Makefile TESTNAME=${TESTNAME} CALIPTRA_TESTNAME=${CALIPTRA_TESTNAME} vcs`
    - NOTE: `TESTNAME=${TESTNAME}` is optional; if not provided, test defaults to value of TESTNAME environment variable, then to `mcu_hello_world`
1. Remaining steps describe how to manually run the individual steps for a VCS simulation
1. [OPTIONAL] By default, this run flow will use the RISC-V toolchain to compile test firmware (according to TESTNAME, CALIPTRA_TESTNAME) into mcu_program.hex, mcu_lmem.hex, mcu_dccm.hex, program.hex, iccm.hex, dccm.hex, and mailbox.hex. 
1. Invoke `${CALIPTRA_ROOT}/tools/scripts/Makefile` with target 'program.hex' to produce SRAM initialization files from the firmware found in `src/integration/test_suites/${TESTNAME}`, `src/integration/test_suites/${CALIPTRA_TESTNAME}` or in `${CALIPTRA_ROOT}/src/integration/test_suites/${CALIPTRA_TESTNAME}`
    - E.g.: `make -f ${CALIPTRA_ROOT}/tools/scripts/Makefile program.hex`
    - NOTE: CALIPTRA_TESTNAME may also be overridden in the makefile command line invocation, e.g. `make -f ${CALIPTRA_ROOT}/tools/scripts/Makefile CALIPTRA_TESTNAME=smoke_test_mbox program.hex`
    - NOTE: The following macro values must be overridden to match the value provided (later) during hardware compilation. The full L0 regression suite includes tests that will fail if the firmware and hardware configuration has a discrepancy. Default values in the Makefile are shown with each macro:
      - CALIPTRA_INTERNAL_TRNG=1
      - E.g. `make -f ${CALIPTRA_ROOT}/tools/scripts/Makefile CALIPTRA_INTERNAL_TRNG=1 program.hex`
1. Invoke `${CALIPTRA_SS_ROOT}/tools/scripts/Makefile` with target 'mcu_program.hex' to produce SRAM initialization files from the firmware found in `src/integration/test_suites/${TESTNAME}`
    - E.g.: `make -f ${CALIPTRA_SS_ROOT}/tools/scripts/Makefile mcu_program.hex`
    - NOTE: TESTNAME may also be overridden in the makefile command line invocation, e.g. `make -f ${CALIPTRA_SS_ROOT}/tools/scripts/Makefile TESTNAME=mcu_hello_world program.hex`
1. Compile complete project using `src/integration/config/caliptra_ss_top_tb.vf` as a compilation target in VCS. When running the `vcs` command to generate simv, users should ensure that `caliptra_ss_top_tb` and `ai3c_tests_bench` are explicitly specified as the top-level components in their command.
    - NOTE: The following macro values must be defined (or omitted) to match the value provided during firmware compilation. The full L0 regression suite includes tests that will fail if the firmware and hardware configuration has a discrepancy.
      - CALIPTRA_INTERNAL_TRNG
1. Copy the test generator scripts to the run output directory:
    - $(CALIPTRA_SS_ROOT)/src/fuse_ctrl/data/otp-img.2048.vmem
    - $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/src/ecc/tb/ecc_secp384r1.exe
    - $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/src/doe/tb/doe_test_gen.py
    - $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/src/sha256/tb/sha256_wntz_test_gen.py
    - $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/submodules/adams-bridge/src/mldsa_top/uvmf/Dilithium_ref/dilithium/ref/test/test_dilithium5
    - $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/submodules/adams-bridge/src/mldsa_top/uvmf/Dilithium_ref/dilithium/ref/test/test_dilithium5_debug
    - $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/src/mldsa/tb/smoke_test_mldsa_vector.hex
1. Simulate project with `caliptra_ss_top_tb` as the top target

## **Regression Tests** ##

### Standalone SystemVerilog Testbench Regression ###
Only tests from existing regression test lists should be run:
* L0 smoke tests: [L0_Promote_caliptra_ss_top_tb_regression.yml](https://github.com/chipsalliance/caliptra-ss/blob/main/src/integration/stimulus/L0_Promote_caliptra_ss_top_tb_regression.yml)
* L1 directed tests: [L1_Nightly_Directed_caliptra_ss_top_tb_regression.yml](https://github.com/chipsalliance/caliptra-ss/blob/main/src/integration/stimulus/L1_Nightly_Directed_caliptra_ss_top_tb_regression.yml)
* L1 random tests: [L1_Nightly_Random_caliptra_ss_top_tb_regression.yml](https://github.com/chipsalliance/caliptra-ss/blob/main/src/integration/stimulus/L1_Nightly_Random_caliptra_ss_top_tb_regression.yml)
