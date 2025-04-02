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

void caliptra_ss_mcu_mbox_write_execute(uint32_t mbox_num, uint32_t value) {
    uint32_t read_payload[16];
    uint32_t write_payload[16];
    
    VPRINTF(LOW, "CALIPTRA: MCU MBOX%x Writing EXECUTE to %x\n", mbox_num, value);
    write_payload[0] = value;
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num, 0, write_payload, 4, 0) ;
}

bool caliptra_ss_mcu_mbox_wait_execute(uint32_t mbox_num, uint32_t expected_value, uint32_t attempt_count) {
    uint32_t read_payload[1];
    uint32_t mbox_data;
    uint32_t mbox_lock_accuired;
    VPRINTF(LOW, "CALIPTRA: MCU MBOX%x WAIT FOR EXECUTE to be %x\n", mbox_num, expected_value);
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
        mbox_data = read_payload[0];
        mbox_data = mbox_data & MCU_MBOX1_CSR_MBOX_EXECUTE_EXECUTE_MASK;
        if(mbox_data == expected_value) {
            return true;
        }
    }
    return false;
}

bool caliptra_ss_mcu_mbox_wait_status_complete(uint32_t mbox_num, uint32_t attempt_count) {
    uint32_t read_payload[1];
    uint32_t mbox_data;
    uint32_t mbox_lock_accuired;
    VPRINTF(LOW, "CALIPTRA: MCU MBOX%x WAIT FOR COMPLETE\n", mbox_num);
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
        mbox_data = read_payload[0];
        mbox_data = mbox_data & MCU_MBOX0_CSR_MBOX_CMD_STATUS_STATUS_MASK;
        VPRINTF(LOW, "CALIPTRA: MBOX%x STATUS: 0x%x\n", mbox_num, mbox_data);
        if (mbox_data == 0x2) {
            return true;
        }
    }
    return false;
}

void caliptra_ss_mcu_mbox_attempt_reads_writes(uint32_t mbox_num) {
    uint8_t fail = 0;
    uint32_t data_length;
    const uint32_t mbox_dlen = 0;
    const uint32_t mbox_cmd = 0x0;
    const uint32_t mbox_user = 0x0;
    uint32_t read_payload[16];
    uint32_t write_payload[16];
    uint32_t mbox_data[0];
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

    if (data_length != mbox_dlen) {
        VPRINTF(FATAL, "CALIPTRA: MCU MBOX%x DLEN not expected value: 0x%x \n", mbox_num, mbox_dlen);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Should be reading all 0's
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
    
    if (data_length != 0x0) {
        VPRINTF(FATAL, "CALIPTRA: MCU MBOX%x CMD_STATUS not expected value: 0x%x \n", mbox_num, 0x0);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Attempting SRAM and CSRs write while MCU has lock
    // Check to see that writes are silently dropped and reads return 0
    VPRINTF(LOW, "CALIPTRA: Attempting Mbox%x SRAM write\n", mbox_num);
    write_payload[0] = 0xDEADBEEF;
    mbox_data[0] = write_payload[0];
    VPRINTF(LOW, "CALIPTRA: Writing to MBOX%x data: 0x%x\n", mbox_num, mbox_data); 
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*5) + MCU_MBOX_NUM_STRIDE * mbox_num, 0, mbox_data, 4, 0);

    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*5) + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
    VPRINTF(LOW, "CALIPTRA: MBOX%x Data[%d]: 0x%x\n", mbox_num, 5, read_payload[0]);
    if (read_payload[0] != 0) {
        VPRINTF(FATAL, "Mbox%x SRAM data from MCU is not expected value - dword: %x expected_data: %x\n",mbox_num, 5, 0);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    VPRINTF(LOW, "CALIPTRA: Attempting MBOX%x Execute write\n", mbox_num);
    write_payload[0] = 1;
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num, 0, write_payload, 4, 0);

    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
    if (read_payload[0] == 1) {
        VPRINTF(FATAL, "Mbox%x MBOX EXECUTE was changed\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    VPRINTF(LOW, "CALIPTRA: Attempting Mbox%x DLEN write\n", mbox_num);
    write_payload[0] = 0xDEADBEEF;
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num, 0, write_payload, 4, 0);

    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
    if (read_payload[0] == 0xDEADBEEF) {
        VPRINTF(FATAL, "Mbox%x DLEN was changed\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    VPRINTF(LOW, "CALIPTRA: Attempting MBOX%x CMD write\n", mbox_num);
    write_payload[0] = 0xDEADBEEF;
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD + MCU_MBOX_NUM_STRIDE * mbox_num, 0, write_payload, 4, 0);

    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
    if (read_payload[0] == 0xDEADBEEF) {
        VPRINTF(FATAL, "Mbox%x CMD was changed\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    VPRINTF(LOW, "CALIPTRA: Attempting MBOX%x CMD_STATUS write\n", mbox_num);
    write_payload[0] = 0xDEADBEEF;
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, 0, write_payload, 4, 0);

    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
    if (read_payload[0] == (0xDEADBEEF & MCU_MBOX0_CSR_MBOX_CMD_STATUS_STATUS_MASK)) {
        VPRINTF(FATAL, "Mbox%x CMD_STATUS was changed\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    VPRINTF(LOW, "CALIPTRA: Attempting MBOX%x USER write\n", mbox_num);
    write_payload[0] = 0xDEADBEEF;
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER + MCU_MBOX_NUM_STRIDE * mbox_num, 0, write_payload, 4, 0);

    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
    if (read_payload[0] == (0xDEADBEEF & MCU_MBOX0_CSR_MBOX_CMD_STATUS_STATUS_MASK)) {
        VPRINTF(FATAL, "Mbox%x MBOX USER was changed\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }   
}

// Test (in conjuction with Caliptra uC C code) does a series of MCU mailbox writes and reads between MCU and Caliptra uC
// 1. Wait for EXECUTE to get set in the MCU MBOX
// 2. Wait for EXECUTE to get cleared. 
// 3. Caliptra will attempt gaining the lock and check that it is locked out for a handful of attempts
// 4. Caliptra will also attempt writes and reads to the SRAM and CSRs that should be unavailable during lock.

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
        // Just for test synchronization have caliptra uC acquire lock first
        caliptra_ss_mcu_mbox_acquire_lock(mbox_num, 100);
        caliptra_ss_mcu_mbox_write_execute(mbox_num, 1);

        if (caliptra_ss_mcu_mbox_wait_status_complete(mbox_num, 200)) {
            caliptra_ss_mcu_mbox_write_execute(mbox_num, 0);    
        } else {
            VPRINTF(FATAL, "CALIPTRA: Timed out waiting for MBOX%x complete\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        // Wait for EXECUTE to get set in the MCU MBOX
        if(!caliptra_ss_mcu_mbox_wait_execute(mbox_num, 1, 1000)) {
            VPRINTF(FATAL, "CALIPTRA: Timed out waiting for MBOX%x execute to be set\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        // Wait for EXECUTE to get cleared in the MCU MBOX
        if(!caliptra_ss_mcu_mbox_wait_execute(mbox_num, 0, 1000)) {
            VPRINTF(FATAL, "CALIPTRA: Timed out waiting for MBOX%x execute to be cleared\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        // Attempt lock acquire (should fail)
        if(caliptra_ss_mcu_mbox_acquire_lock(mbox_num, 5)) {
            VPRINTF(FATAL, "CALIPTRA: Acquired MBOX%x lock while zeroization is going on\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        VPRINTF(LOW, "CALIPTRA: Lock acquire failed (intentionally) for MBOX%x \n", mbox_num);

        caliptra_ss_mcu_mbox_attempt_reads_writes(mbox_num);

        VPRINTF(LOW, "CALIPTRA: Sequence complete\n");

        SEND_STDOUT_CTRL(0xff);
}
