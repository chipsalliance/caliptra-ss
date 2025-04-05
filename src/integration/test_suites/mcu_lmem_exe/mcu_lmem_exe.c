//********************************************************************************
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
//********************************************************************************
#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include <string.h>
#include <stdint.h>

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

static const char* mcu_sram_msg __attribute__ ((section(".mcu_sram.msg"))) = "=================\nHello World from MCU SRAM\n=================\n";
void mcu_sram_print_msg (void) __attribute__ ((aligned(4),section (".mcu_sram.print_msg")));

void mcu_sram_print_msg (void) {
    VPRINTF(LOW, mcu_sram_msg);
}

void main (void) {
    int argc=0;
    char *argv[1];
    uint32_t reg_data;

    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_RESET_REASON) & MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_MASK) {
        mcu_sram_print_msg();
        SEND_STDOUT_CTRL(0xFF);
        while(1);
    } else {
        VPRINTF(LOW, "=================\nMCU: MCU SRAM Exec Test\n=================\n\n")

        VPRINTF(LOW, "MCU: Bringing Caliptra out of Reset\n");
        mcu_cptra_init_d(.cfg_mcu_fw_sram_exec_reg_size=true, .mcu_fw_sram_exec_reg_size=0x8000);

        VPRINTF(LOW, "\nMCU: Wait for Caliptra reset req...\n");
        mcu_mci_poll_exec_lock();
        VPRINTF(LOW, "MCU: Observed Caliptra reset req; issuing reset\n\n");
        mcu_mci_req_reset();
        while(1);
    }
}
