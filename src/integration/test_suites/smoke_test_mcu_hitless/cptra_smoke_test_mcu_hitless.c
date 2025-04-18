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
        int argc=0;
        char *argv[1];
        uint32_t reg;
        uint32_t read_payload[16];
        uint32_t data_length;
        uint32_t write_payload[16];
        mbox_op_s op;

        uint32_t mbox_num = decode_single_valid_mbox();

        VPRINTF(LOW, "----------------------------------\nCaliptra: MCU Hitless Update  !!\n----------------------------------\n", mbox_num);

        //set ready for FW so tb will push FW
        soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

        // Wait for MCU to send Message to Caliptra Mailbox to "Process FW Update in MCU Mbox SRAM"
        // wait for mailbox data avail
        VPRINTF(LOW, "Caliptra: Wait for Caliptra Mailbox Execute\n");
        if(!cptra_wait_for_cptra_mbox_execute(10000)) {
            VPRINTF(FATAL, "Caliptra: Caliptra MBOX execute not set\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        //read mbox command
        // 0x1234 is sample command for "Process FW Update in MCU Mbox SRAM"
        op = soc_ifc_read_mbox_cmd();
        if (op.cmd != 0x1234) {
            VPRINTF(FATAL, "Caliptra: Caliptra Mbox CMD not expected value: 0x%x \n", 0x1234);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        // Test case: verify MCU Mbox user id is SoC Agent
        if(cptra_mcu_mbox_read_mbox_user(mbox_num) != 0x12345678) {
            VPRINTF(FATAL, "Caliptra: MCU Mbox%x User ID not expected value: 0x%x \n", mbox_num, 0x12345678);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        // Do some MCU MBOX SRAM reads (to mimic hash processing, etc)
        //read from mbox
        uint32_t dlen = cptra_mcu_mbox_read_dlen(mbox_num);
        VPRINTF(LOW, "Caliptra: DLEN from MCU mailbox: 0x%x\n", dlen);

        uint32_t data = cptra_mcu_mbox_read_dword_sram(mbox_num, 0);
        data = cptra_mcu_mbox_read_dword_sram(mbox_num, (dlen/2)/4-1);
        data = cptra_mcu_mbox_read_dword_sram(mbox_num, dlen/4-1);

        //set complete status
        VPRINTF(LOW, "Caliptra: Set cmd complete status\n");
        lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS, CMD_COMPLETE);

        // HACK: Set FW_EXEC_CTRL[2] to emulate that MCU was already running out of MCU SRAM
        VPRINTF(LOW, "CALIPTRA: Setting FW_EXEC_CTRL[2]\n");
        lsu_write_32(CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0, 0x4);

        // HACK: needed to clear posedge indication that would be cleared after FW_BOOT_UPD reset
        VPRINTF(LOW, "CALIPTRA: Clearing FW_EXEC_CTRL[2]\n");
        lsu_write_32(CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0, 0x0);

        // Wait for MCU to clear interrupt
        cptra_wait_mcu_reset_req_interrupt_clear(10000);

        // HACK: Set FW_EXEC_CTRL[2] to emulate that MCU was already running out of SRAM
        VPRINTF(LOW, "CALIPTRA: Setting FW_EXEC_CTRL[2]\n");
        lsu_write_32(CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0, 0x4);
        // Clear FW_EXEC_CTRL[2] to indicate hitless update is ready
        VPRINTF(LOW, "FW: Clearing FW_EXEC_CTRL[2]\n");
        lsu_write_32(CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0, 0x0);

        // Wait for MCU to clear interrupt
        cptra_wait_mcu_reset_req_interrupt_clear(10000);

        // Wait for MCU RESET STATUS to be set
        cptra_wait_mcu_reset_status_set(10000);

        // Copy the image from the mailbox SRAM to the MCU SRAM
        uint32_t sram_base_addr = cptra_get_mcu_sram_execution_region_start();
        uint32_t mbox_sram_data;
        for (uint32_t ii = 0; ii < dlen/4; ii++) {
            mbox_sram_data = cptra_mcu_mbox_read_dword_sram(mbox_num, ii);
            VPRINTF(LOW, "CALIPTRA: Writing to MBOX%x SRAM[%d]: 0x%x\n", mbox_num, ii, mbox_sram_data);
            cptra_axi_dword_write(sram_base_addr + 4*ii, mbox_sram_data);
        }

        // Set RESET_REASON to indicate hitless update
        VPRINTF(LOW, "Caliptra: Setting RESET_REASON.FW_HITLESS_UPD_RESET\n");
        cptra_axi_dword_write(SOC_MCI_TOP_MCI_REG_RESET_REASON, MCI_REG_RESET_REASON_FW_HITLESS_UPD_RESET_MASK);

        // Set FW_EXEC_CTRL[2] to indicate hitless update is ready
        VPRINTF(LOW, "Caliptra: Setting FW_EXEC_CTRL[2]\n");
        lsu_write_32(CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0, 0x4);

        VPRINTF(LOW, "CALIPTRA: Sequence complete\n");

        while(1);
}
