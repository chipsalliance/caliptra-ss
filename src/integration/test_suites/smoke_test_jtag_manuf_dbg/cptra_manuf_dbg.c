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
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include "soc_ifc.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"


#define exp_mbox_cmd                0x4d445554
#define MBOX_DLEN_VAL               9 // This plus 4 is for checksum
uint32_t read_TOKEN[9];
uint32_t exp_token[9] = {
    0xFFFFF8E2,
    0xABCDEFEB,
    0x00000000,
    0x00000000,
    0x00000000,
    0x00000000,
    0x00000000,
    0x00000000,
    0xF888888A
};


/*
#### Debug Unlock
1. On reset, the ROM checks if the `MANUF_DBG_UNLOCK_REQ` bit in the `SS_DBG_SERVICE_REG_REQ` register and the `DEBUG_INTENT` bit in `SS_DEBUG_INTENT` register are set.

2. If they are set, the ROM sets the `TAP_MAILBOX_AVAILABLE` bit in the `SS_DBG_SERVICE_REG_RSP` register, then enters a loop, awaiting a `TOKEN` command on the mailbox. The payload of this command is a 256-bit value.

3. Upon receiving the `TOKEN` command, ROM sets the `SS_DBG_SERVICE_REG_RSP` register `MANUF_DBG_UNLOCK_IN_PROGRESS` bit to 1.

4. The ROM performs a SHA-512 operation on the token to generate the input token digest.

5. The ROM compares the `FUSE_MANUF_DBG_UNLOCK_TOKEN` fuse register with the input token digest.

6. The ROM completes the mailbox command.

7. If the input token digest and fuse token digests match, the ROM authorizes the debug unlock by setting the `SS_DBG_SERVICE_REG_RSP` register `MANUF_DBG_UNLOCK_SUCCESS` bit to 1.

8. If the token digests do not match, the ROM blocks the debug unlock by setting the the `SS_DBG_SERVICE_REG_RSP` register `MANUF_DBG_UNLOCK_FAIL` bit to 1.

9. The ROM sets the `SS_DBG_SERVICE_REG_RSP` register `MANUF_DBG_UNLOCK_IN_PROGRESS` bit to 0.
*/


volatile uint32_t* stdout           = (uint32_t *)STDOUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile uint32_t  intr_count;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};



void mailbox_available() {
    // sets the `TAP_MAILBOX_AVAILABLE` bit in the `SS_DBG_SERVICE_REG_RSP` register
    //make tap mailbox available
    uint32_t status_reg ;
    VPRINTF(LOW, "CLP_CORE: detected MANUF DEBUG request...\n");
    status_reg = SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_TAP_MAILBOX_AVAILABLE_MASK;
    status_reg = status_reg | SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_IN_PROGRESS_MASK;
    VPRINTF(LOW, "CLP_CORE: set MANUF_DBG_UNLOCK_IN_PROGRESS...\n");
    VPRINTF(LOW, "CLP_CORE: set MAILBOX_AVAILABLE...\n");
    lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP, status_reg);
    return;
}

void wait_for_token() {
    //check cmd
    //Poll status until fsm is in EXECUTE UC
    uint32_t state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
    while (state != MBOX_EXECUTE_UC) {
      state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
    }
    VPRINTF(LOW, "CLP_CORE: Checking cmd from tap\n");
    uint32_t  read_data = lsu_read_32(CLP_MBOX_CSR_MBOX_CMD);
    if (read_data != exp_mbox_cmd) {
        VPRINTF(ERROR, "ERROR: mailbox command mismatch actual (0x%x) expected (0x%x)\n", read_data, exp_mbox_cmd);
    }

    VPRINTF(LOW, "CLP_CORE: cmd from tap is 0x%08X\n", read_data);
    return;
}

void compare_token() {
    // read SOC_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN
    // compare based on that set either fail or success
    uint32_t status_reg ;
    VPRINTF(LOW, "CLP_CORE: Checking %d bytes from tap\n", MBOX_DLEN_VAL*4);
    int ii;
    for (ii = 0; ii < MBOX_DLEN_VAL; ii++) {
        read_TOKEN[ii] = soc_ifc_mbox_read_dataout_single();
        VPRINTF(LOW, "CLP_CORE: mailbox data (0x%x)\n", read_TOKEN[ii]);
        // ROM needs to perform HASH comperision in here.
        if (read_TOKEN[ii] != exp_token[ii]) {
            VPRINTF(ERROR, "ERROR: mailbox data mismatch actual (0x%x) expected (0x%x)\n", read_TOKEN[ii], exp_token[ii]);
            lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP, SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_FAIL_MASK);
            status_reg = lsu_read_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP);
            status_reg = status_reg & (SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_IN_PROGRESS_MASK ^ 0xFFFFFFFF);
            lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP, status_reg);
            SEND_STDOUT_CTRL( 0x1);
        };
    }
    lsu_write_32(CLP_MBOX_CSR_TAP_MODE,0);
    soc_ifc_clear_execute_reg();
    status_reg = lsu_read_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP);
    status_reg = status_reg | SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_MASK;
    lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP, status_reg);
    VPRINTF(LOW, "\n\nCLP_CORE: set MANUF_DBG_UNLOCK_SUCCESS high...\n\n");
    status_reg = lsu_read_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP);
    status_reg = status_reg & (SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_IN_PROGRESS_MASK ^ 0xFFFFFFFF);
    lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP, status_reg);
    // deassert in_progress
    return;
}

void main(void) {
    int argc=0;
    char *argv[1];

    VPRINTF(LOW,"----------------------------------\nCaliptra: Mimicking ROM from Subsystem!!\n----------------------------------\n");
    uint32_t status_reg = 0;
    status_reg = (lsu_read_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ) & SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_MANUF_DBG_UNLOCK_REQ_MASK) == SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_MANUF_DBG_UNLOCK_REQ_MASK;
    if (status_reg){
        mailbox_available();
        wait_for_token();
        compare_token();
        while(1);
    } else {
        VPRINTF(LOW, "CLP_CORE: Error because there is no MANUF DEBUG request...\n");
        printf("%c",0xff); //End the test
    } 

}
