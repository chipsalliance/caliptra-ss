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
#include "caliptra_ss_lib.h"
#include "caliptra_ss_defines.h"
#include "mcu_isr.h"
#include "riscv-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"



volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
volatile uint32_t  intr_count;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = MEDIUM;
#endif

volatile mcu_intr_received_s mcu_intr_rcv = {0};

uint32_t main(void) {
        int argc=0;
        char *argv[1];

        uint32_t mci_notif_intr_count = 0;
        uint32_t mci_notif_intr_count_hw = 0;
        uint32_t mci_error_intr_count = 0;
        uint32_t mci_error_intr_count_hw = 0;
        uint32_t i3c_intr_count = 0;
        uint32_t i3c_intr_count_hw = 0;
        uint64_t mtime = 0;

        VPRINTF(LOW,"----------------------------------\nMCU: Direct ISR Test!!\n----------------------------------\n");

        // Setup the interrupt CSR configuration
        init_interrupts();

        // Initialize the counter
        intr_count = 0;

        // Trigger each intr bit and sleep in between triggers to allow ISR to execute and show idle time in sims
        VPRINTF(MEDIUM,"MCU: Trigger MCI Error0 Intr\n");
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MCU_SRAM_DMI_AXI_COLLISION_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_INTERNAL_TRIG_MASK                  ); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX0_ECC_UNC_TRIG_MASK             ); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX1_ECC_UNC_TRIG_MASK             ); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_WDT_TIMER1_TIMEOUT_TRIG_MASK        ); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_WDT_TIMER2_TIMEOUT_TRIG_MASK        ); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);

        VPRINTF(MEDIUM,"MCU: Trigger MCI Error1 Intr\n");
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL31_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL30_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL29_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL28_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL27_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL26_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL25_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL24_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL23_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL22_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL21_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL20_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL19_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL18_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL17_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL16_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL15_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL14_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL13_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL12_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL11_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL10_TRIG_MASK); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL9_TRIG_MASK ); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL8_TRIG_MASK ); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL7_TRIG_MASK ); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL6_TRIG_MASK ); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL5_TRIG_MASK ); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL4_TRIG_MASK ); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL3_TRIG_MASK ); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL2_TRIG_MASK ); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL1_TRIG_MASK ); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_ERROR_AGG_ERROR_FATAL0_TRIG_MASK ); mci_error_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);

        VPRINTF(MEDIUM,"MCU: Trigger MCI Notif0 Intr\n");
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MCU_SRAM_ECC_COR_TRIG_MASK    ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_CPTRA_MCU_RESET_REQ_TRIG_MASK ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_GEN_IN_TOGGLE_TRIG_MASK       ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_TARGET_DONE_TRIG_MASK   ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_TARGET_DONE_TRIG_MASK   ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_CMD_AVAIL_TRIG_MASK     ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_CMD_AVAIL_TRIG_MASK     ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_CPTRA_MBOX_CMD_AVAIL_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_ECC_COR_TRIG_MASK       ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_ECC_COR_TRIG_MASK       ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_DEBUG_LOCKED_TRIG_MASK        ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_SCAN_MODE_TRIG_MASK           ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_SOC_REQ_LOCK_TRIG_MASK  ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_SOC_REQ_LOCK_TRIG_MASK  ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_OTP_OPERATION_DONE_TRIG_MASK  ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);

        VPRINTF(MEDIUM,"MCU: Trigger MCI Notif1 Intr\n");
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL31_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL30_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL29_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL28_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL27_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL26_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL25_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL24_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL23_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL22_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL21_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL20_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL19_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL18_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL17_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL16_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL15_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL14_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL13_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL12_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL11_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL10_TRIG_MASK); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL9_TRIG_MASK ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL8_TRIG_MASK ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL7_TRIG_MASK ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL6_TRIG_MASK ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL5_TRIG_MASK ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL4_TRIG_MASK ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL3_TRIG_MASK ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL2_TRIG_MASK ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL1_TRIG_MASK ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_NOTIF_AGG_ERROR_NON_FATAL0_TRIG_MASK ); mci_notif_intr_count++; __asm__ volatile ("wfi") /* "Wait for interrupt" */; mcu_sleep(100);

        // TODO i3c triggers ?

        // Disable interrutps
        csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);

        // Print interrupt count from FW/HW trackers
        // MCI Error
        VPRINTF(MEDIUM, "MCU: MCI Err fw count: 0x%x\n", mci_error_intr_count);
        mci_error_intr_count_hw =  lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R    ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R                      ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R                 ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R                 ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R            ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R            ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R             ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R              ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R              ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R              ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R              ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R              ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R              ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R              ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R              ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R              ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R );
        VPRINTF(MEDIUM, "MCU: MCI Err hw count: 0x%x\n", mci_error_intr_count_hw);
        if (mci_error_intr_count != mci_error_intr_count_hw) {
            VPRINTF(ERROR, "MCU: MCI Error count mismatch! 0x%x 0x%x\n", mci_error_intr_count, mci_error_intr_count_hw);
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }

        // MCI Notif
        VPRINTF(MEDIUM, "MCU: MCI Ntf fw count: 0x%x\n", mci_notif_intr_count);
        mci_notif_intr_count_hw =  lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R     ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R  ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R        ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R    ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R    ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R      ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R      ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R        ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R        ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R         ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R            ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R   ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R   ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_OTP_OPERATION_DONE_INTR_COUNT_R   ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R ) +
                                   lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R );
        VPRINTF(MEDIUM, "MCU: MCI Ntf hw count: 0x%x\n", mci_notif_intr_count_hw);
        if (mci_notif_intr_count != mci_notif_intr_count_hw) {
            VPRINTF(ERROR, "MCU: MCI Notif count mismatch! 0x%x 0x%x\n", mci_notif_intr_count, mci_notif_intr_count_hw);
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }

        // Print total interrupt count
        VPRINTF(MEDIUM, "MCU: main intr trig end - intr_cnt:0x%x\n", intr_count);
        if (intr_count != mci_error_intr_count_hw + mci_notif_intr_count_hw) {
            VPRINTF(ERROR, "TOTAL count mismatch!\n");
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }

        // Now test timer interrupts
        VPRINTF(MEDIUM, "MCU: Test timer int\n");
        mtime = ((uint64_t) lsu_read_32(SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_H) << 32) | lsu_read_32(SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_L);
        // Did we just rollover? Maybe the value read from MTIME_H was stale after reading MTIME_L.
        // Reread.
        if ((mtime & 0xFFFFFFFF) < 0x40) {
            mtime = ((uint64_t) lsu_read_32(SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_H) << 32) | lsu_read_32(SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_L);
        }

        // Setup a wait time of 1000 clock cycles = 10us
        mtime += 1000;
        lsu_write_32(SOC_MCI_TOP_MCI_REG_MCU_RV_MTIMECMP_L, mtime & 0xFFFFFFFF);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_MCU_RV_MTIMECMP_H, mtime >> 32       );

        // Re-enable interrupts (but not external interrupts)
        csr_clr_bits_mie(MIE_MEI_BIT_MASK);
        csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);

        // Poll for Timer Interrupt Handler to complete processing.
        // Timer ISR simply sets mtimecmp back to max values, so poll for that.
        // A simulation can never hit this value naturally, because it's a 64b timer and will
        // timeout.
        while (lsu_read_32(SOC_MCI_TOP_MCI_REG_MCU_RV_MTIMECMP_H) != 0xFFFFFFFF) {
            // Sleep in between triggers to allow ISR to execute and show idle time in sims
            mcu_sleep(100);
        }

        return 0;
}

