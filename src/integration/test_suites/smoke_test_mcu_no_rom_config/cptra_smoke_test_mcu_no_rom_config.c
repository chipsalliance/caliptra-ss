// SPDX-License-Identifier: Apache-2.0
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
#include "soc_address_map.h"
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "caliptra_ss_lib.h"
#include "riscv-csr.h"
#include "veer-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include "printf.h"
#include "soc_ifc.h"
#include "soc_ifc_ss.h"
#include "caliptra_reg.h"

volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Test (in conjuction with Caliptra uC C code) exercises the hitless flow 
// 
// -SOC BFM will acquire mbox lock (standing in as proxy for soc agent)
// -SOC BFM load FW image in to mailbox (pre-compiled image)
// -MCU will set target user (to Caliptra uC) and target user valid; send caliptra mailbox cmd? to process
// -Caliptra uC reads and processes image (in this case, just read do a few reads for testing purpose
// -Caliptra set interrupt for notif_cptra_mcu_reset_req_sts 
// -Caliptra clears FW_EXEC_CTRL[2] indicating a FW image is ready for MCU.
// -MCU sees request from Caliptra clears the interrupt status.
// -MCU sets RESET_REQUEST.mcu_req in MCI to request a hitless reset 
// -Caliptra polls on RESET_STATUS.MCU_RESET to see that reset is complete
// -Caliptra will gain access to MCU SRAM Updatable Execution Region and update the FW image.
// -Caliptra sets RESET_REASON.FW_HITLESS_UPD_RESET
// -Caliptra sets FW_EXEC_CTRL[2]
// -MCU is brought out of reset and checks MCI's RESET_REASON
// -MCU jumps to MCU SRAM
// -MCU new firmware will print out hello world/look at boolean flag and stored in hitless image in SRAM and pass the test if it is FW_HITLESS_UPD_RESET

void main(void) {
        VPRINTF(LOW, "----------------------------------\nCaliptra: MCU Hitless Update  !!\n----------------------------------\n");

        // HACK: Set FW_EXEC_CTRL[2] to do FW_BOOT_UPD_RESET first so MCU HW tracking looks like FW_BOOT has been done
        VPRINTF(LOW, "CALIPTRA: Setting FW_EXEC_CTRL[2]\n");
        lsu_write_32(CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0, 0x4);

        // Wait for MCU to clear interrupt
        cptra_wait_mcu_reset_req_interrupt_clear(10000);

        // Clear FW_EXEC_CTRL[2] to indicate hitless update is ready
        VPRINTF(LOW, "CALIPTRA: Clearing FW_EXEC_CTRL[2]\n");
        lsu_write_32(CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0, 0x0);

        // Wait for MCU RESET STATUS to be set
        cptra_wait_mcu_reset_status_set(10000);

        VPRINTF(LOW, "CALIPTRA: Sequence complete\n");

        while(1);
}
