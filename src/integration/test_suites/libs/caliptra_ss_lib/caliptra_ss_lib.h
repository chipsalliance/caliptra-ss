// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
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

#ifndef CALIPTRA_SS_LIB
#define CALIPTRA_SS_LIB


extern uint32_t state;
uint32_t xorshift32(void);

void reset_fc_lcc_rtl(void);
void mcu_mci_boot_go();
void mcu_cptra_fuse_init();
void mcu_cptra_user_init();
void mcu_cptra_poll_mb_ready();
void mcu_cptra_mbox_cmd();

#define FC_LCC_CMD_OFFSET 0xB0
#define CMD_FC_LCC_RESET                FC_LCC_CMD_OFFSET + 0x02
#define CMD_FORCE_FC_AWUSER_CPTR_CORE   FC_LCC_CMD_OFFSET + 0x03
#define CMD_FORCE_FC_AWUSER_MCU         FC_LCC_CMD_OFFSET + 0x04
#define CMD_RELEASE_AWUSER              FC_LCC_CMD_OFFSET + 0x05
#define CMD_FC_FORCE_ZEROIZATION        FC_LCC_CMD_OFFSET + 0x06
#define CMD_FC_FORCE_ZEROIZATION_RESET  FC_LCC_CMD_OFFSET + 0x07
#define CMD_RELEASE_ZEROIZATION         FC_LCC_CMD_OFFSET + 0x08
#define CMD_FORCE_LC_TOKENS             FC_LCC_CMD_OFFSET + 0x09
#define CMD_LC_FORCE_RMA_SCRAP_PPD      FC_LCC_CMD_OFFSET + 10

#endif // CALIPTRA_SS_LIB
