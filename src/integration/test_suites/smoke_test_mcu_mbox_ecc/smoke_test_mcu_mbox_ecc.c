//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
// 
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

void main (void) {
    int argc=0;
    char *argv[1];

    uint32_t mbox_addr[16];
    uint32_t mbox_dlen;

    uint32_t mbox_num = decode_single_valid_mbox();

    mcu_cptra_init_d();

    ////////////////////////////////////
    // Mailbox ECC test
    // 1) MCU to acquire Mbox Lock
    // 2) Enable ECC single bit injection
    // 3) Write random data to random addresses in Mbox SRAM 
    // 4) Set execute and read back same addresses from Mbox SRAM
    // 5) Check SB ECC status bit and interrupt.  RW1C to interrupt
    // 6) Clear execute.  Check that ECC status registers are cleared.
    // 7) Reacquire lock
    // 6) Enable ECC double bit error injection
    // 7) Write random data to random addresses in Mbox SRAM 
    // 8) Set execute and read back same addresses from Mbox SRAM
    // 9) Check final DB ECC status bit, error interrupt and HW_ERROR_NON_FATAL reg. RW1C to interrupt
    // 10) Set and clear execute.  Check that ECC status registers are cleared.

    // MBOX: clear the lock on MBOX that is there from reset
    mcu_mbox_clear_lock_out_of_reset(mbox_num);

    // Clear interrupts.  Test does checking in some cases that only ECC interrupts are set
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R, 0xffffffff);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R, 0xffffffff);

    VPRINTF(LOW, "=================\nMCU MBOX%x ECC Test\n=================\n", mbox_num);

    // MBOX: Acquire lock
    if (!mcu_mbox_acquire_lock(mbox_num, 1000)) {
        VPRINTF(FATAL, "MCU: Mbox%x didn't acquire lock\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);        
    }

    // MBOX: Enable ECC single bit injection
    SEND_STDOUT_CTRL(TB_CMD_INJECT_MBOX_SRAM_SINGLE_ECC_ERROR);

    uint32_t sram_size_kb = mcu_mbox_get_sram_size_kb(mbox_num);

    // Single write to SRAM (Due to timing, ECC injector won't inject error on first write)
    mcu_mbox_write_sram_dword(mbox_num, xorshift32() % (sram_size_kb * 256), xorshift32());

    uint32_t rand_dword_addr;
    uint32_t rand_data;

    for (uint32_t i = 0; i < (sizeof(mbox_addr)/sizeof(uint32_t)); i++) {
        rand_data = xorshift32();
        rand_dword_addr = xorshift32() % (sram_size_kb * 256);
        mbox_addr[i] = rand_dword_addr;
        mcu_mbox_write_sram_dword(mbox_num, rand_dword_addr, rand_data);
    }

    // Write short Dlen for test run time
    mcu_mbox_write_dlen(mbox_num, 200);

    // Setting execute
    mcu_mbox_set_execute(mbox_num);

    for (uint32_t i = 0; i < (sizeof(mbox_addr)/sizeof(uint32_t)); i++) {
        rand_dword_addr = mbox_addr[i];
        rand_data = mcu_mbox_read_sram_dword(mbox_num, rand_dword_addr);

        // Check if SB ECC interrupt has been logged
        // R1WC to clear interrupt
        if (!is_only_mcu_mbox_sb_ecc_interrupt_set(mbox_num)) {
            VPRINTF(FATAL, "MCU: Mbox%x SB ECC interrupt not set\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        clear_mcu_mbox_clear_sb_ecc_interrupt(mbox_num);
    }

    // Check if SB ECC status has been logged
    if (mcu_mbox_read_hw_status(mbox_num) == MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_SINGLE_ERROR_MASK) {
        VPRINTF(LOW, "MCU: Mbox%x SB ECC detected\n", mbox_num);
    } else {
        VPRINTF(FATAL, "MCU: Mbox%x No SB ECC detected or DB ECC also set\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Clear execute
    mcu_mbox_clear_execute(mbox_num);

    // Re-acquire lock before checking that status is cleared (need zeroization to complete)
    if (!mcu_mbox_acquire_lock(mbox_num, 1000)) {
        VPRINTF(FATAL, "MCU: Mbox%x didn't acquire lock\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);        
    }

    // Check that ECC status registers are cleared
    if (mcu_mbox_read_hw_status(mbox_num) != 0) {
        VPRINTF(FATAL, "MCU: Mbox%x SB ECC status not cleared\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // MBOX: Enable ECC double bit injection
    SEND_STDOUT_CTRL(TB_CMD_DISABLE_MBOX_SRAM_ECC_ERROR_INJECTION);
    SEND_STDOUT_CTRL(TB_CMD_INJECT_MBOX_SRAM_DOUBLE_ECC_ERROR);
 
     // Single write to SRAM (Due to timing, ECC injector won't inject error on first write)
    mcu_mbox_write_sram_dword(mbox_num, xorshift32() % (sram_size_kb * 256), xorshift32());

    // Write random SRAM data to random addreses and read them back
    for (uint32_t i = 0; i < (sizeof(mbox_addr)/sizeof(uint32_t)); i++) {
        rand_data = xorshift32();
        rand_dword_addr = xorshift32() % (sram_size_kb * 256);
        mbox_addr[i] = rand_dword_addr;
        mcu_mbox_write_sram_dword(mbox_num, rand_dword_addr, rand_data);
    }

    // Write short Dlen for test run time
    mcu_mbox_write_dlen(mbox_num, 100);

    for (uint32_t i = 0; i < (sizeof(mbox_addr)/sizeof(uint32_t)); i++) {
        rand_dword_addr = mbox_addr[i];
        rand_data = mcu_mbox_read_sram_dword(mbox_num, rand_dword_addr);

        // Check if DB ECC interrupt has been logged
        // R1WC to clear interrupt
        if (!is_only_mcu_mbox_db_ecc_interrupt_set(mbox_num)) {
            VPRINTF(FATAL, "MCU: Mbox%x DB ECC interrupt not set\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        clear_mcu_mbox_clear_db_ecc_interrupt(mbox_num);
    }

    // Check if DB ECC status has been logged
    if (mcu_mbox_read_hw_status(mbox_num) == MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_DOUBLE_ERROR_MASK) {
        VPRINTF(LOW, "MCU: Mbox%x DB ECC detected\n", mbox_num);
    } else {
        VPRINTF(FATAL, "MCU: Mbox%x No DB ECC detected or SB ECC also set\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Check HW_ERROR_NON_FATAL register
    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_HW_ERROR_NON_FATAL) == 
        (MCI_REG_HW_ERROR_NON_FATAL_MBOX0_ECC_UNC_MASK << mbox_num)) {
        VPRINTF(LOW, "MCU: Mbox%x DB ECC detected in HW_ERROR_NON_FATAL\n", mbox_num);
    } else {
        VPRINTF(FATAL, "MCU: Mbox%x No DB ECC detected (or other unexpected bits were set) in HW_ERROR_NON_FATAL\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Try clearing HW_ERROR_NON_FATAL
    lsu_write_32(SOC_MCI_TOP_MCI_REG_HW_ERROR_NON_FATAL, MCI_REG_HW_ERROR_NON_FATAL_MBOX0_ECC_UNC_MASK << mbox_num);
    // Check that HW_ERROR_NON_FATAL register is cleared
    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_HW_ERROR_NON_FATAL) != 0) {
        VPRINTF(FATAL, "MCU: Mbox%x HW_ERROR_NON_FATAL not cleared\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Set and clear execute (set is done later in DB case to test that hw_status still is reflected during lock)
    mcu_mbox_set_execute(mbox_num);
    mcu_mbox_clear_execute(mbox_num);

    // Re-acquire lock before checking that status is cleared (need to wait until zeroization to complete)
    if (!mcu_mbox_acquire_lock(mbox_num, 1000)) {
        VPRINTF(FATAL, "MCU: Mbox%x didn't acquire lock\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);        
    }

    // Check that ECC status registers are cleared
    if (mcu_mbox_read_hw_status(mbox_num) & MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_DOUBLE_ERROR_MASK) {
        VPRINTF(FATAL, "MCU: Mbox%x DB ECC status not cleared\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    if (mcu_mbox_read_hw_status(mbox_num) & MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_SINGLE_ERROR_MASK) {
        VPRINTF(FATAL, "MCU: Mbox%x SB ECC status not cleared\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    SEND_STDOUT_CTRL(0xff);
}
