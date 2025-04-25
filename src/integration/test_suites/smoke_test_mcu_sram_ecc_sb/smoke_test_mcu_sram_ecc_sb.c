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
#include "mci.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include <string.h>
#include <stdint.h>
#include <stdarg.h> // For va_list, va_start, va_end


volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void enable_ecc() {
    VPRINTF(LOW, "Enabling ECC...\n");
    SEND_STDOUT_CTRL(TB_CMD_INJECT_MCU_SRAM_SINGLE_ECC_ERROR);
    VPRINTF(LOW, "ECC enabled.\n");
}

void enable_interrupts() {
    VPRINTF(LOW, "Enabling interrupts for MCU SRAM ECC...\n");

    // Read the current value of the interrupt enable register
    uint32_t intr_enable_reg = lsu_read_32((uintptr_t)SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R);

    // Set the bit for MCU SRAM ECC correctable error interrupt enable
    intr_enable_reg |= MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MCU_SRAM_ECC_COR_EN_MASK;

    // Write the updated value back to the register
    lsu_write_32((uintptr_t)SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R, intr_enable_reg);

    // Verify if the interrupt enable bit was set correctly
    uint32_t verify_reg = lsu_read_32((uintptr_t)SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R);
    if (!(verify_reg & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MCU_SRAM_ECC_COR_EN_MASK)) {
        handle_error("Failed to enable MCU SRAM ECC correctable error interrupt.");
    }

    
    intr_enable_reg = lsu_read_32((uintptr_t)SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R);
    
    intr_enable_reg |= MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK;
    
    // Write the updated value back to the register
    lsu_write_32((uintptr_t)SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R, intr_enable_reg);

    VPRINTF(LOW, "Interrupts for MCU SRAM ECC enabled successfully.\n");
}

void write_random_data_to_sram() {
    VPRINTF(LOW, "Starting to write random data to SRAM...\n");
    uint32_t start = get_mcu_sram_protected_region_start();
    uint32_t end = get_mcu_sram_protected_region_end();
    uint32_t range = end - start;

    if (range == 0) {
        handle_error("Invalid SRAM range.");
    }

    uint32_t base_random = xorshift32(); // Generate a base random value

    for (int i = 0; i < 10; i++) { // Write to 10 random addresses
        uint32_t random_address = start + (base_random % range) & ~0x3; // Align to 4 bytes
        uint32_t random_data = base_random + i; // Derive subsequent random data from base_random
        VPRINTF(LOW, "Writing 0x%08X to address 0x%08X\n", random_data, random_address);
        lsu_write_32(random_address, random_data);

        // Read back and verify
        uint32_t read_data = lsu_read_32(random_address);
        if (read_data != random_data) {
            handle_error("Data mismatch at address 0x%08X: wrote 0x%08X, read 0x%08X\n",
                    random_address, random_data, read_data);
        } else {
            VPRINTF(LOW, "Data verified at address 0x%08X: 0x%08X\n", random_address, read_data);
        }

        base_random = xorshift32(); // Update base_random for the next iteration
    }
    VPRINTF(LOW, "Finished writing random data to SRAM.\n");
}

void check_ecc_error_status() {
    VPRINTF(LOW, "Checking ECC err status...\n");

    uint32_t notif_reg = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R);
    if (!(notif_reg & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MCU_SRAM_ECC_COR_STS_MASK)) {
        handle_error("Expected ECC correctable error status not set in NOTIF0_INTR_T.");
    } else {
        VPRINTF(LOW, "ECC correctable err status set as expected.\n");
    }

    VPRINTF(LOW, "Finished checking ECC err status.\n");
}

void clear_ecc_error_status() {
    VPRINTF(LOW, "Clearing ECC err status...\n");

    // Clear the ECC error status registers
    lsu_write_32((uintptr_t)SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R, 
                 MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MCU_SRAM_ECC_COR_STS_MASK);


    uint32_t notif_reg = lsu_read_32((uintptr_t)SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R);
    if (notif_reg & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MCU_SRAM_ECC_COR_STS_MASK) {
        handle_error("Failed to clear ECC correctable error status in SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R.");
    }

    VPRINTF(LOW, "ECC err status cleared successfully.\n");
}

void main (void) {

    VPRINTF(LOW, "Starting ECC test...\n");

    // Step 1: Enable ECC
    enable_ecc();

    // Step 2: Enable interrupts for ECC
    enable_interrupts();

    // Step 3: Write random data to random addresses in SRAM
    write_random_data_to_sram();

    // Step 4 & 5: Check ECC error status
    check_ecc_error_status();

    // Step 6 & 7: Clear ECC error status
    clear_ecc_error_status();

    VPRINTF(LOW, "ECC test completed.\n");

    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);

}
