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


#define AUTH_DEBUG_UNLOCK_REQ_CMD     0x50445552
#define AUTH_DEBUG_UNLOCK_TOKEN       0x50445554


volatile uint32_t* stdout           = (uint32_t *)STDOUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile uint32_t  intr_count;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};


uint8_t debug_level;
uint32_t checksum, ii, lenght_challenge;
uint32_t expected_unlock_req_payload[2];
uint32_t expected_token_payload[0x753];
uint32_t challenge_payload[] = {
    4294966978,      // checksum
    22,              // length
    0, 0, 0, 0,      // unique_device_identifier[0..3]
    0, 0, 0, 0,      // unique_device_identifier[4..7]
    0x01020304,      // challenge[0]
    0x05060708,      // challenge[1]
    0x090A0B0C,      // challenge[2]
    0x0D0E0F10,      // challenge[3]
    0x11121314,      // challenge[4]
    0x15161718,      // challenge[5]
    0x191A1B1C,      // challenge[6]
    0x1D1E1F20,      // challenge[7]
    0x21222324,      // challenge[8]
    0x25262728,      // challenge[9]
    0x292A2B2C,      // challenge[10]
    0x2D2E2F30       // challenge[11]
};

uint32_t PROD_dbg_pk[] = {
    0x01020304,      // PROD_dbg_pk[0]
    0x05060708,      // PROD_dbg_pk[1]
    0x090A0B0C,      // PROD_dbg_pk[2]
    0x0D0E0F10,      // PROD_dbg_pk[3]
    0x11121314,      // PROD_dbg_pk[4]
    0x15161718,      // PROD_dbg_pk[5]
    0x191A1B1C,      // PROD_dbg_pk[6]
    0x1D1E1F20,      // PROD_dbg_pk[7]
    0x21222324,      // PROD_dbg_pk[8]
    0x25262728,      // PROD_dbg_pk[9]
    0x292A2B2C,      // PROD_dbg_pk[10]
    0x2D2E2F30       // PROD_dbg_pk[11]
};


enum mbox_status_e status;

uint32_t dma_read_from_lsu(uint32_t address){
    uint32_t read_data;
    soc_ifc_axi_dma_read_ahb_payload(address, 0, &read_data, 4, 0);
    return read_data;
}

void wait_for_mailbox_cmd() {
    uint32_t status_reg ;
    status_reg = SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_TAP_MAILBOX_AVAILABLE_MASK;
    status_reg = status_reg | SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_PROD_DBG_UNLOCK_IN_PROGRESS_MASK;
    lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP, status_reg);
    VPRINTF(LOW, "CLP_CORE: set PROD_DBG_UNLOCK_IN_PROGRESS...\n");
    VPRINTF(LOW, "CLP_CORE: set MAILBOX_AVAILABLE...\n");
    // DEBUG UNLOCK should be in in-progress, write a register

    uint32_t state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
    while (state != MBOX_EXECUTE_UC) {
        state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
    }

    VPRINTF(LOW, "CLP_CORE: Checking cmd from tap\n");
    uint32_t cmd = lsu_read_32(CLP_MBOX_CSR_MBOX_CMD);
    if (cmd != AUTH_DEBUG_UNLOCK_REQ_CMD) {
        status_reg = SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_PROD_DBG_UNLOCK_FAIL_MASK;
        lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP, status_reg);
        VPRINTF(ERROR, "ERROR: mailbox command mismatch actual (0x%x) expected (0x%x)\n", cmd, AUTH_DEBUG_UNLOCK_REQ_CMD);
        printf("%c", 0x01);
    }
    VPRINTF(LOW, "CLP_CORE: Received expected mailbox cmd 0x%08X\n", cmd);
}

void read_unlock_req_payload() {
    VPRINTF(LOW, "CLP_CORE: Reading AUTH_DEBUG_UNLOCK_REQ payload...\n");
    checksum = soc_ifc_mbox_read_dataout_single();
    VPRINTF(LOW, "CLP_CORE: Received checksum 0x%08X\n", checksum);

    for (int i = 0; i < 2; ++i) {
        expected_unlock_req_payload[i] = soc_ifc_mbox_read_dataout_single();
    }

    uint32_t length         = expected_unlock_req_payload[0];
    debug_level    = expected_unlock_req_payload[1] & 0xFF;

    VPRINTF(LOW, "| Field         | Size (bytes) | Value     |\n");
    VPRINTF(LOW, "|---------------|--------------|-----------|\n");
    VPRINTF(LOW, "| Length        | 4            | 0x%08X |\n", length);
    VPRINTF(LOW, "| Unlock Level  | 1            | 0x%02X     |\n", debug_level);
}

void send_challenge_response() {

    lenght_challenge = 21;
    lsu_write_32(CLP_MBOX_CSR_MBOX_DLEN, (lenght_challenge + 1) * 4); // This +1 is for the checksum

    VPRINTF(LOW, "CLP_CORE: Writing %d bytes to mailbox\n", (21 + 1) * 4);

    lsu_write_32(CLP_MBOX_CSR_MBOX_DATAIN, challenge_payload[0]);
    VPRINTF(LOW, "CLP_CORE:  checksum: 0x%x\n", challenge_payload[0]);
    for (ii = 0; ii < 21; ++ii) {
        lsu_write_32(CLP_MBOX_CSR_MBOX_DATAIN, challenge_payload[ii]);
    }
    // soc_ifc_clear_execute_reg();
    status = DATA_READY;
    soc_ifc_set_mbox_status_field(status);
    VPRINTF(LOW, "CLP_CORE: Challenge response sent.\n");
}

void wait_and_read_token() {
    uint32_t state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
    while (state != MBOX_EXECUTE_UC) {
        state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
    }
    VPRINTF(LOW, "CLP_CORE: Checking cmd from tap\n");
    uint32_t cmd = lsu_read_32(CLP_MBOX_CSR_MBOX_CMD);
    if (cmd != AUTH_DEBUG_UNLOCK_TOKEN) {
        VPRINTF(ERROR, "ERROR: mailbox command mismatch actual (0x%x) expected (0x%x)\n", cmd, AUTH_DEBUG_UNLOCK_TOKEN);
        lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP, SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_PROD_DBG_UNLOCK_FAIL_MASK);
        printf("%c", 0x01);
    }
    VPRINTF(LOW, "CLP_CORE: Received expected mailbox cmd 0x%08X\n", cmd);
    VPRINTF(LOW, "CLP_CORE: Reading AUTH_DEBUG_UNLOCK_TOKEN payload...\n");
    checksum = soc_ifc_mbox_read_dataout_single();
    VPRINTF(LOW, "CLP_CORE: Received checksum 0x%08X\n", checksum);

    for (int i = 0; i < 1/*0x753*/; ++i) {
        expected_token_payload[i] = soc_ifc_mbox_read_dataout_single();
    }
}


void read_pk_hash() {
    uint32_t numOfPK = lsu_read_32(CLP_SOC_IFC_REG_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES);
    uint32_t offSet = lsu_read_32(CLP_SOC_IFC_REG_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET);

    VPRINTF(LOW, "CLP_CORE: Number of debug PK hashes = %d\n", numOfPK);
    VPRINTF(LOW, "CLP_CORE: PK hash register bank offset = 0x%08X\n", offSet);

    uint32_t pk_hash;
    uint32_t base_address = offSet + 12 * (debug_level - 1) * 4;

    for (int i = 0; i < 12; i++) {
        uint32_t addr = base_address + (i * 4);
        pk_hash = dma_read_from_lsu(addr);
        VPRINTF(LOW, "CLP_CORE: reading PROD_dbg_pk[%02d] from address 0x%08X = 0x%08X\n", i, addr, pk_hash);
        if (PROD_dbg_pk[i] != pk_hash) {
            VPRINTF(LOW, "CLP_CORE: MISMATCH at index %02d! Expected: 0x%08X, Read: 0x%08X\n", i, PROD_dbg_pk[i], pk_hash);
        }
    }
}



void main(void) {
    VPRINTF(LOW,"----------------------------------\nCaliptra: Mimicking ROM from Subsystem!!\n----------------------------------\n");
    
    uint32_t state = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_SECURITY_STATE);
    uint32_t is_production = (state & SOC_IFC_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_MASK) == 0x3;
    if (!is_production) {
        VPRINTF(ERROR, "CLP_CORE: Not in production mode\n");
        printf("%c", 0x01);
        return;
    }

    uint32_t req_reg = lsu_read_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ);
    uint32_t intent = lsu_read_32(CLP_SOC_IFC_REG_SS_DEBUG_INTENT);
    if ((req_reg == SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ_PROD_DBG_UNLOCK_REQ_MASK) && intent) {
        VPRINTF(LOW, "CLP_CORE: PROD DEBUG UNLOCK request detected\n");
        wait_for_mailbox_cmd();
        read_unlock_req_payload();
        send_challenge_response();
        wait_and_read_token();
        read_pk_hash();
        uint32_t status_reg = lsu_read_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP);
        status_reg = status_reg | SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_PROD_DBG_UNLOCK_SUCCESS_MASK;
        lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP, status_reg);
        VPRINTF(LOW, "\n\nCLP_CORE: set PROD_DBG_UNLOCK_SUCCESS high...\n\n");
        status_reg = lsu_read_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP);
        status_reg = status_reg & (SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_PROD_DBG_UNLOCK_IN_PROGRESS_MASK ^ 0xFFFFFFFF);
        lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP, status_reg);
        lsu_write_32(CLP_MBOX_CSR_TAP_MODE,0);
        VPRINTF(LOW, "CLP_CORE: Token received and test complete.\n");
        while(1); // Do not complete the execution, wait for MCU terminal cmd
    } else {
        VPRINTF(ERROR, "CLP_CORE: No debug unlock request or intent not set\n");
        printf("%c", 0xFF);
    }
}
