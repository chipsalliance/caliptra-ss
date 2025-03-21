// SPDX-License-Identifier: Apache-2.0
<<<<<<< HEAD
// Copyright 2020 Western Digital Corporation or its affiliates.
=======
>>>>>>> 37691f4be06052eb741ac8b254fc416cfb1c2de0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

<<<<<<< HEAD
=======
<<<<<<< HEAD:src/integration/testbench/sv_tests/ai3c/ai3c_test_includes.svh
`include "cptra_ss_i3c_core_defines.svh"
`include "cptra_ss_i3c_core_base_test.svh"
`include "i3c_reg_rd_wr.svh"
`include "i3c_sboot.svh"
`include "ai3ct_ext_basic.svh"
=======
>>>>>>> 37691f4be06052eb741ac8b254fc416cfb1c2de0
#ifndef CALIPTRA_SS_LIB
#define CALIPTRA_SS_LIB

void reset_rtl(void);
void mcu_mci_boot_go();
void mcu_cptra_fuse_init();
void mcu_cptra_user_init();
void mcu_cptra_poll_mb_ready();
void mcu_cptra_mbox_cmd();
<<<<<<< HEAD
void boot_mcu_with_fuses();
void boot_mcu();
void boot_i3c_core(void);
void boot_i3c_socmgmt_if(void);
void boot_i3c_standby_ctrl_mode();
void boot_i3c_reg(void);

#endif // CALIPTRA_SS_LIB
=======

#endif // CALIPTRA_SS_LIB
>>>>>>> 37691f4be06052eb741ac8b254fc416cfb1c2de0:src/integration/test_suites/libs/caliptra_ss_lib/caliptra_ss_lib.h
>>>>>>> 37691f4be06052eb741ac8b254fc416cfb1c2de0
