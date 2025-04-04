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
#include "caliptra_defines.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include <stdint.h>
#include "printf.h"
#include "caliptra_isr.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity             verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity             verbosity_g = LOW;
#endif

#define MBOX_DLEN_VAL             0x00000020

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main () {

    mbox_op_s op;
    uint32_t ii;
    uint32_t data;
    enum mbox_fsm_e state;
    uint32_t mbox_data[] = { 0x00000000,
                             0x11111111,
                             0x22222222,
                             0x33333333,
                             0x44444444,
                             0x55555555,
                             0x66666666,
                             0x77777777 };
    uint32_t read_data;

    // Message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " Caliptra Bringup (in CSS)!!\n"    );
    VPRINTF(LOW, "----------------------------------\n");

    //set ready for FW so tb will push FW
    soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

    // Sleep
    for (uint16_t slp = 0; slp < 33; slp++);

    //wait for mailbox data avail
    VPRINTF(LOW, "FW: Wait\n");
    while((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) != MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);

    //read mbox command
    op = soc_ifc_read_mbox_cmd();

    //read from mbox
    VPRINTF(LOW, "FW: Reading %d bytes from mailbox\n", op.dlen);
    while(op.dlen) {
        data = soc_ifc_mbox_read_dataout_single();
        VPRINTF(HIGH, "  dataout: 0x%x\n", data);
        if (op.dlen < 4) {
            op.dlen=0;
        } else {
            op.dlen-=4;//sizeof(uint32_t);
        }
    }

    //push new data in like a response
    VPRINTF(LOW, "FW: Writing %d bytes to mailbox\n", MBOX_DLEN_VAL);
    for (ii = 0; ii < MBOX_DLEN_VAL/4; ii++) {
        VPRINTF(HIGH, "  datain: 0x%x\n", mbox_data[ii]);
        lsu_write_32(CLP_MBOX_CSR_MBOX_DATAIN,mbox_data[ii]);
    }

    //set data ready status
    VPRINTF(LOW, "FW: Set data ready status\n");
    lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS,DATA_READY);

    //check FSM state, should be in EXECUTE_SOC
    state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
    if (state != MBOX_EXECUTE_SOC) {
        VPRINTF(ERROR, "ERROR: mailbox in unexpected state (%x) when expecting MBOX_EXECUTE_SOC (0x%x)\n", state, MBOX_EXECUTE_SOC);
        SEND_STDOUT_CTRL( 0x1);
        while(1);
    } else {
        VPRINTF(LOW, "FW: Mailbox in expected state, MBOX_EXECUTE_SOC\n");
    }

    //Wait for SoC to reset execute reg
    VPRINTF(LOW, "FW: Wait for SoC to reset execute register\n");
    while((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) == 1);

    VPRINTF(LOW, "FW: Setting MCI FW_BOOT_UPD\n");
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCI_REG_RESET_REASON, 0, MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_MASK, 4,0);
    
    // Set FW EXEC REGION LOCK to enable MCU SRAM check
    VPRINTF(LOW, "FW: Setting FW_EXEC_CTRL\n");
    lsu_write_32(CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0, 0x4);

    // Wait for MCU test to finish and end sim
    while(1);
}
