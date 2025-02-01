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
_*Last Update: 2024/09/17*_

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
   - `avery/2023.2` AXI interconnect and I3C VIP
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
│   ├── i3c-core
│   ├── integration
│   ├── lc_ctrl
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
Verilog file lists are generated via VCS and included in the config directory for each unit. New files added to the design must be included in the vf list. They can be included manually or by using VCS to regenerate the vf file. File lists define the compilation sources (including all dependencies) required to build and simulate a given module or testbench, and should be used by integrators for simulation, lint, and synthesis.
