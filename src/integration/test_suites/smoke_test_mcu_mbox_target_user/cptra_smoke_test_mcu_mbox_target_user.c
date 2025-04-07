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
#include "caliptra_reg.h"

volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

bool caliptra_ss_mcu_mbox_acquire_lock(uint32_t mbox_num, uint32_t attempt_count) {
    uint32_t read_payload[1];
    uint32_t mbox_data;
    uint32_t mbox_lock_accuired;
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
        mbox_data = read_payload[0];
        mbox_lock_accuired = mbox_data & MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK;
        if(mbox_lock_accuired == 0) {
            return true;
        }
    }
    return false;
}

bool caliptra_ss_mcu_mbox_wait_target_user_valid(uint32_t mbox_num, uint32_t attempt_count) {
    uint32_t read_payload[1];
    uint32_t mbox_data;
    VPRINTF(LOW, "CALIPTRA: MCU MBOX%x WAIT FOR TARGET USER VALID\n", mbox_num);
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
        mbox_data = read_payload[0];
        mbox_data = mbox_data & MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID_VALID_MASK;
        if(mbox_data) {
            return true;
        }
    }
    return false;
}

bool caliptra_ss_mcu_mbox_wait_execute(uint32_t mbox_num, uint32_t attempt_count) {
    uint32_t read_payload[1];
    uint32_t mbox_data;
    uint32_t mbox_lock_accuired;
    VPRINTF(LOW, "CALIPTRA: MCU MBOX%x WAIT FOR EXECUTE to be SET\n", mbox_num);
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
        mbox_data = read_payload[0];
        mbox_data = mbox_data & MCU_MBOX1_CSR_MBOX_EXECUTE_EXECUTE_MASK;
        if( mbox_data) {
            return true;
        }
    }
    return false;
}

// Get MCU MBOX data from SRAM and CSRs and check it against expected values.
void caliptra_ss_mcu_mbox_get_and_check_sram_data_and_csrs(uint32_t mbox_num, uint32_t expected_mbox_dlen, uint32_t *mcu_expected_data) {
    uint32_t data_length;
    const uint32_t mbox_cmd = 0xFADECAFE;
    const uint32_t mbox_user = 0x1;  // TODO should be MCU strap
    uint32_t read_payload[16];
    uint32_t write_payload[16];
    uint32_t mbox_data[0];
    
    VPRINTF(LOW, "CALIPTRA: Reading MBOX%x CMD\n", mbox_num);
    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
    data_length = read_payload[0];
    VPRINTF(LOW, "CALIPTRA: CMD: 0x%x\n", data_length);

    if (data_length != mbox_cmd) {
        VPRINTF(FATAL, "CALIPTRA: MCU MBOX%x CMD not expected value: 0x%x \n", mbox_num, mbox_cmd);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    VPRINTF(LOW, "CALIPTRA: Checking MBOX% USER\n", mbox_num);
    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
    data_length = read_payload[0];
    VPRINTF(LOW, "CALIPTRA: MBOX0 USER = %x\n", data_length);
    
    if (data_length != mbox_user) {
        VPRINTF(FATAL, "CALIPTRA: MCU MBOX0 MBOX USER not expected value: 0x%x \n", mbox_user);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    VPRINTF(LOW, "CALIPTRA: Reading MBOX%x DLEN\n", mbox_num);
    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
    data_length = read_payload[0];
    VPRINTF(LOW, "CALIPTRA: Mbox%x DLEN: 0x%x\n", mbox_num, data_length);

    if (data_length != expected_mbox_dlen) {
        VPRINTF(FATAL, "CALIPTRA: MCU MBOX%x DLEN: 0x%x Expected value: 0x%x \n", mbox_num, data_length, expected_mbox_dlen);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    VPRINTF(LOW, "CALIPTRA: Reading MBOX%x Data\n", mbox_num);
    for (uint8_t ii = 0; ii < data_length/4; ii++) {
        soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*ii) + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
        VPRINTF(LOW, "CALIPTRA: MBOX%x Data[%d]: 0x%x\n", mbox_num, ii, read_payload[0]);
        if (read_payload[0] != mcu_expected_data[ii]) {
            VPRINTF(FATAL, "Mbox%x SRAM data from MCU is not expected value - dword: %x expected_data: %x\n", mbox_num, ii, mcu_expected_data[ii]);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
    }

    VPRINTF(LOW, "CALIPTRA: Checking Mbox%x CMD_STATUS \n", mbox_num);
    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
    data_length = read_payload[0];
    VPRINTF(LOW, "CALIPTRA: MBOX%x CMD STATUS = %x\n", mbox_num, data_length);
    
    if (data_length != MCU_MBOX_DATA_READY) {
        VPRINTF(FATAL, "CALIPTRA: MCU MBOX%x CMD_STATUS not expected value: 0x%x \n", mbox_num, 0x1);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}

// Write to the MBOX SRAM and CSRs and check to see if the writes were successful or not
// For SRAM and DLEN it will depend on the can_write flag. If can_write is true, the writes should be successful.
void caliptra_ss_mcu_mbox_target_write_sram_and_csrs(uint32_t mbox_num, uint32_t mbox_dlen, uint32_t *clptra_write_data, bool can_write) {
    bool error;
    uint32_t data_length;
    const uint32_t mbox_cmd = 0xFADECAFE;
    const uint32_t mbox_user = 0x1;  // TODO should be MCU strap
    uint32_t read_payload[16];
    uint32_t write_payload[16];
    uint32_t mbox_data[0];

    // Attempting SRAM and CSRs write
    // Check to see that writes occurred (if writing allowed) or are silently dropped and reads return 0
    VPRINTF(LOW, "CALIPTRA: Attempting Mbox%x SRAM writes\n", mbox_num);
    for (uint8_t ii = 0; ii < mbox_dlen/4; ii++) {
        if (can_write) {
            write_payload[0] = clptra_write_data[ii];
        } else {
            write_payload[0] = 0xDEADBEEF;
        }
        VPRINTF(LOW, "CALIPTRA: Writing to MBOX%x data: 0x%x\n", mbox_num, write_payload[0]); 
        mbox_data[0] = write_payload[0];
        soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*ii) + MCU_MBOX_NUM_STRIDE * mbox_num, 0, mbox_data, 4, 0);

        soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*ii) + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
        VPRINTF(LOW, "CALIPTRA: MBOX%x Data[%d]: 0x%x\n", mbox_num, ii, read_payload[0]);
        
        error = (can_write) ? (read_payload[0] != clptra_write_data[ii]) : (read_payload[0] != 0);
        if (error) {
            VPRINTF(FATAL, "Mbox%x SRAM data from MCU is not expected value - dword: %x expected_data: %x\n",mbox_num, ii, 0);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
    }

    VPRINTF(LOW, "CALIPTRA: Attempting MBOX%x Execute write\n", mbox_num);
    write_payload[0] = 0;
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num, 0, write_payload, 4, 0);

    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
    if (read_payload[0] == 0) {
        VPRINTF(FATAL, "Mbox%x MBOX EXECUTE was changed\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    uint32_t dlen_write_value = (can_write) ? mbox_dlen : 0xDEADBEEF;
    write_payload[0] = dlen_write_value;
    VPRINTF(LOW, "CALIPTRA: Attempting Mbox%x DLEN write: 0x%x\n", mbox_num, write_payload[0]);
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num, 0, write_payload, 4, 0);

    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
    
    error = (can_write) ? (read_payload[0] != mbox_dlen) : (read_payload[0] == 0xDEADBEEF);
    if (error) {
        VPRINTF(FATAL, "Mbox%x DLEN was changed unexpectedly: 0x%x\n", mbox_num, read_payload[0]);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    write_payload[0] = 0xDEADBEEF;
    VPRINTF(LOW, "CALIPTRA: Attempting MBOX%x CMD write: 0x%x\n", mbox_num, write_payload[0]);
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD + MCU_MBOX_NUM_STRIDE * mbox_num, 0, write_payload, 4, 0);

    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
    if (read_payload[0] == 0xDEADBEEF) {
        VPRINTF(FATAL, "Mbox%x CMD was changed: 0x%x\n", mbox_num, read_payload[0]);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    write_payload[0] = 0xDEADBEEF;
    VPRINTF(LOW, "CALIPTRA: Attempting MBOX%x CMD_STATUS write: 0x%x\n", mbox_num, write_payload[0]);
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, 0, write_payload, 4, 0);

    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
    if (read_payload[0] == (0xDEADBEEF & MCU_MBOX0_CSR_MBOX_CMD_STATUS_STATUS_MASK)) {
        VPRINTF(FATAL, "Mbox%x CMD_STATUS was changed: 0x%x\n", mbox_num, read_payload[0]);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    write_payload[0] = 0xDEADBEEF;
    VPRINTF(LOW, "CALIPTRA: Attempting MBOX%x USER write: 0x%x\n", mbox_num, write_payload[0]);
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER + MCU_MBOX_NUM_STRIDE * mbox_num, 0, write_payload, 4, 0);

    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
    if (read_payload[0] == (0xDEADBEEF & MCU_MBOX0_CSR_MBOX_CMD_STATUS_STATUS_MASK)) {
        VPRINTF(FATAL, "Mbox%x MBOX USER was changed: 0x%x\n", mbox_num, read_payload[0]);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    } 

    // Attempt TARGET_USER write
    write_payload[0] = 0xdeadbeef;
    VPRINTF(LOW, "CALIPTRA: Attempting MCU MBOX%x TARGET_USER write: 0x%x\n", mbox_num, write_payload[0]);
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER + MCU_MBOX_NUM_STRIDE * mbox_num, 0, write_payload, 4, 0);

    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
    data_length = read_payload[0];

    if (data_length == 0xdeadbeef) {
        VPRINTF(FATAL, "CALIPTRA: MCU MBOX%x TARGET_USER was able to be writen by USER: 0x%x \n", mbox_num, data_length);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Attempt TARGET_USER_VALID write
    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
    data_length = read_payload[0] & MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID_VALID_MASK;
    VPRINTF(LOW, "CALIPTRA: Current MCU MBOX%x TARGET_USER_VALID value: 0x%x\n", mbox_num, data_length);

    write_payload[0] = ~data_length & MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID_VALID_MASK;
    VPRINTF(LOW, "CALIPTRA: Attempting MCU MBOX%x TARGET_USER_VALID write: 0x%x\n", mbox_num, write_payload[0]);
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID + MCU_MBOX_NUM_STRIDE * mbox_num, 0, write_payload, 4, 0);

    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
    data_length = read_payload[0];

    if (data_length == write_payload[0]) {
        VPRINTF(FATAL, "CALIPTRA: MCU MBOX%x TARGET_USER_VALID was able to be writen by USER: 0x%x \n", mbox_num, 0);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}

// Test (in conjuction with Caliptra uC C code) exercise the TARGET_USER aspects of the MCU Mbox 
// Caliptra uC will be the target user
// 1. MCU acquires Mbox lock and writes information in the mailbox CSRs and SRAM and sets execute (without setting target user)
// 2. MCU will set TARGET_USER but not TARGET_USER_VALID and set execute
// 3. Caliptra uC will wait for execute and attempt writing/reading SRAM and writing CSRs (all of which should fail)
// 4. Caliptra uC will attempt acquiring lock (as a sync point so MCU can see if any contents were able to be changed).
// 4. MCU will set TARGET_USER_VALID
// 5. Caliptra uC will read the mailbox CSRs and SRAM and check that the data is what was written by the MCU
// 6. Caliptra uC will attempt to write to the mailbox CSRs and SRAM and set TARGET_STATUS/DONE
// 7. MCU will check that only SRAM and DLEN has changed 

void main(void) {
        int argc=0;
        char *argv[1];
        uint32_t reg;
        uint32_t read_payload[16];
        uint32_t data_length;
        uint32_t write_payload[16];
        #ifdef MCU_MBOX_VALID_VECTOR
            uint32_t mbox_instances = MCU_MBOX_VALID_VECTOR;
        #else
            uint32_t mbox_instances = 0;
        #endif

        uint32_t mbox_num = 0;
        if (mbox_instances == 0x2) {
            mbox_num = 1;
        }

        VPRINTF(LOW, "----------------------------------\nSmoke Test MCI MBOX%x  !!\n----------------------------------\n", mbox_num);

        if(!caliptra_ss_mcu_mbox_wait_execute(mbox_num, 1000)) {
            VPRINTF(FATAL, "CALIPTRA: Timed out waiting for MBOX%x execute\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        // Reading SRAM and CSRs and then attempt writes.  Caliptra as target user is still not valid
        // Since user doesn't have a lock expected data should be 0
        uint32_t mcu_expected_data[] = { 0x00000000,
                                        0x00000000,
                                        0x00000000,
                                        0x00000000,
                                        0x00000000,
                                        0x00000000,
                                        0x00000000,
                                        0x00000000,
                                        0x00000000,
                                        0x00000000,
                                        0x00000000,
                                        0x00000000,
                                        0x00000000,
                                        0x00000000,
                                        0x00000000,
                                        0x00000000 };
        caliptra_ss_mcu_mbox_get_and_check_sram_data_and_csrs(mbox_num, sizeof(mcu_expected_data), mcu_expected_data);

        // Attempt to write to SRAM and CSRs.
        // Since user doesn't have a lock writes should not take affect.
        bool target_valid = false;
        caliptra_ss_mcu_mbox_target_write_sram_and_csrs(mbox_num, sizeof(mcu_expected_data), mcu_expected_data, target_valid);

        // Attempt to acquire lock even though MCU has the lock (as a sync point for the self-checking on the MCU side)
        caliptra_ss_mcu_mbox_acquire_lock(mbox_num, 1);

        // Wait for TARGET_USER_VALID to be set
        if(!caliptra_ss_mcu_mbox_wait_target_user_valid(mbox_num, 100000)){
            VPRINTF(FATAL, "CALIPTRA: Timed out waiting for MBOX%x target user valid\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        // Get the data written by MCU in mailbox and check expected data and CSRs
        uint32_t mcu_expected_data_after_target[] = { 0x00000000,
                                                        0x11111111,
                                                        0x22222222,
                                                        0x33333333,
                                                        0x44444444,
                                                        0x55555555,
                                                        0x66666666,
                                                        0x77777777,
                                                        0x88888888,
                                                        0x99999999,
                                                        0xaaaaaaaa,
                                                        0xbbbbbbbb,
                                                        0xcccccccc,
                                                        0xdddddddd,
                                                        0xeeeeeeee,
                                                        0xffffffff };
       
        caliptra_ss_mcu_mbox_get_and_check_sram_data_and_csrs(mbox_num, sizeof(mcu_expected_data_after_target), mcu_expected_data_after_target);

        uint32_t clptra_write_data[] = { 0x10101010,
                                        0x20202020,
                                        0x30303030,
                                        0x40404040,
                                        0x50505050,
                                        0x60606060,
                                        0x70707070,
                                        0x80808080,
                                        0x90909090,
                                        0xA0A0A0A0,
                                        0xB0B0B0B0,
                                        0xC0C0C0C0,
                                        0xD0D0D0D0,
                                        0xE0E0E0E0,
                                        0xF0F0F0F0,
                                        0x12345678,
                                        0x86754321};

        // Attempt writes again (SRAM and DLEN should succeed)
        // CSRs should not be able to be written to - can_write is set
        target_valid = true;
        caliptra_ss_mcu_mbox_target_write_sram_and_csrs(mbox_num, sizeof(clptra_write_data), clptra_write_data, target_valid);

        // Set TARGET_STATUS DONE and COMPLETE
        VPRINTF(LOW, "CALIPTRA: Set TARGET_USER_STATUS Done in MBOX%x with CMD_COMPLETE\n", mbox_num);
        write_payload[0] = MCU_MBOX0_CSR_MBOX_TARGET_STATUS_DONE_MASK |
                            MCU_MBOX_TARGET_STATUS_COMPLETE >> MCU_MBOX0_CSR_MBOX_TARGET_STATUS_STATUS_LOW;
        soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, 0, write_payload, 4, 0);

        VPRINTF(LOW, "CALIPTRA: Sequence complete\n");

        while(1);
}
