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
#include <stdlib.h>
#include "caliptra_isr.h"
#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include <string.h>
#include <stdint.h>
#include "caliptra_ss_lib.h"
#include "wdt.h"
#include "veer-csr.h"

// volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
volatile uint32_t  intr_count = 0;
volatile uint32_t  rst_count  = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

#ifdef PLAYBOOK_RANDOM_SEED
    unsigned time = (unsigned) PLAYBOOK_RANDOM_SEED;
#else
    unsigned time = 0;
#endif

volatile uint32_t * mci_error0_intr_en  = (uint32_t *) SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R; //TODO: confirm
volatile uint32_t * mci_error1_intr_en  = (uint32_t *) SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R;
volatile uint32_t * mci_notif0_intr_en  = (uint32_t *) SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R;
volatile uint32_t * mci_notif1_intr_en  = (uint32_t *) SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R;
volatile uint32_t * mci_global_intr_en  = (uint32_t *) SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void nmi_handler (void);
void service_mci_error_intr();

void nmi_handler (void) {
    VPRINTF(LOW, "*** Entering NMI Handler ***\n");
    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL) & MCI_REG_HW_ERROR_FATAL_NMI_PIN_MASK) {
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);
    }
    else {
        VPRINTF(ERROR, "Unexpected entry into NMI handler function\n");
    }
}

void service_dmi_axi_collision_error_intr() {
    printf("Polling for collision err bit\n");
    while (!(lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MCU_SRAM_DMI_AXI_COLLISION_STS_MASK))
    //Clear intr
    printf("clearing collision err bit\n");
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R, MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MCU_SRAM_DMI_AXI_COLLISION_STS_MASK);
}

void service_mbox0_ecc_unc_error_intr() {
    printf("Polling for mbox0_ecc_unc_err bit\n");
    while (!(lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX0_ECC_UNC_STS_MASK))
    //Clear intr
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R, MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX0_ECC_UNC_STS_MASK);
}

void service_mbox1_ecc_unc_error_intr() {
    printf("Polling for mbox1_ecc_unc_err bit\n");
    while (!(lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX1_ECC_UNC_STS_MASK))
    //Clear intr
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R, MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX1_ECC_UNC_STS_MASK);
}

void service_agg_error_fatal_intr() {
    uint32_t data = 0;
    while (!data) {
        data = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R);
    }
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R, data);
}

void service_agg_error_non_fatal_intr() {
    uint32_t data = 0;
    while (!data) {
        data = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R);
    }
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R, data);
}

void service_notif0_intr() {
    uint32_t data = 0;
    while (!data) {
        data = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R);
    }
    printf("\nnotif0 intr data = %x\n", data);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R, data);
}

uint32_t main(void) {
    uint8_t rand_mask_sel;
    uint32_t data = 0;

    VPRINTF(LOW, "---------------------------\n");
    VPRINTF(LOW, " Err Handling Smoke Test\n");
    VPRINTF(LOW, "---------------------------\n");

    srand(time);

    //Enable SOC notif interrupt
    *mci_error0_intr_en = MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MCU_SRAM_DMI_AXI_COLLISION_EN_MASK | MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_INTERNAL_EN_MASK | MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX0_ECC_UNC_EN_MASK | MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX1_ECC_UNC_EN_MASK | MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_MASK | MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_MASK;
    *mci_error1_intr_en = 0xffff;
    *mci_notif0_intr_en = 0xffff;
    *mci_notif1_intr_en = 0xffff;
    *mci_global_intr_en = MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK | MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK;
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR, (uint32_t) (nmi_handler));

    rst_count++;
    VPRINTF(LOW, "------------\nrst_count = %0d\n------------\n", rst_count)

    if (rst_count == 1) {
        VPRINTF(LOW, "------------\nMCI err without mask\n------------\n");
        SEND_STDOUT_CTRL(TB_CMD_INJECT_MCI_ERROR_FATAL);

        for (uint8_t i = 0; i < 100; i++); //wait for all error injections to be done
        //service intr
        service_dmi_axi_collision_error_intr();
        printf("done servicing collision err bit");

        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);
        //halt core function
        csr_write_mpmc_halt();
    }
    else if (rst_count == 2) {
        VPRINTF(LOW, "------------\nMCI err with mask\n------------\n");
        rand_mask_sel = rand() % 0x8; //% 8 since there are 3 mask bits and 2**3 combinations
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK, rand_mask_sel);
        SEND_STDOUT_CTRL(TB_CMD_INJECT_MCI_ERROR_FATAL);

        for (uint8_t i = 0; i < 100; i++); //wait for all error injections to be done
        //service intr
        service_dmi_axi_collision_error_intr();
        printf("done servicing collision err bit\n");

        // for (uint8_t i = 0; i < 10; i++);
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);
        csr_write_mpmc_halt();
    }
    else if (rst_count == 3) {
        VPRINTF(LOW, "------------\nMCI non-ftl err without mask\n------------\n");
        SEND_STDOUT_CTRL(TB_CMD_INJECT_MCI_ERROR_NON_FATAL);

        service_mbox0_ecc_unc_error_intr();
        printf("done servicing mbox0 err bit\n");

        service_mbox1_ecc_unc_error_intr();
        printf("done servicing mbox1 err bit\n");

        //Add other stuff here
        VPRINTF(LOW, "------------\nMCI non-ftl err with mask\n------------\n");
        rand_mask_sel = rand() % 0x4; //% 4 since there are 2 mask bits and 2**2 combinations
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK, rand_mask_sel);
        SEND_STDOUT_CTRL(TB_CMD_INJECT_MCI_ERROR_NON_FATAL);

        service_mbox0_ecc_unc_error_intr();
        printf("done servicing mbox0 err bit\n");
        service_mbox1_ecc_unc_error_intr();
        printf("done servicing mbox1 err bit\n");

        VPRINTF(LOW, "------------\nAggregate ftl err without mask\n------------\n");
        SEND_STDOUT_CTRL(TB_CMD_INJECT_AGG_ERROR_FATAL);

        service_agg_error_fatal_intr();
        printf("Done servicing agg err ftl\n");

        //issue cold reset to clear fatal flag
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);
        csr_write_mpmc_halt();
    }
    else if (rst_count == 4) {
        VPRINTF(LOW, "-------------\nAggregate ftl err with mask\n---------------\n");
        rand_mask_sel = rand() % 32;
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK, rand_mask_sel);
        SEND_STDOUT_CTRL(TB_CMD_INJECT_AGG_ERROR_FATAL);

        service_agg_error_fatal_intr();
        printf("Done servicing agg err ftl\n");

        //issue warm reset to clear fatal flag
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        csr_write_mpmc_halt();
    }
    else if (rst_count == 5) {
        VPRINTF(LOW, "-------------\nAggregate non ftl err without mask\n---------------\n");
        SEND_STDOUT_CTRL(TB_CMD_INJECT_AGG_ERROR_NON_FATAL);

        service_agg_error_non_fatal_intr();
        printf("Done servicing agg err non ftl\n");

        //issue warm reset to clear fatal flag
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        csr_write_mpmc_halt();
    }
    else if (rst_count == 6) {
        VPRINTF(LOW, "-------------\nAggregate non ftl err with mask\n---------------\n");
        rand_mask_sel = rand() % 32;
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK, rand_mask_sel);
        SEND_STDOUT_CTRL(TB_CMD_INJECT_AGG_ERROR_NON_FATAL);

        service_agg_error_non_fatal_intr();
        printf("Done servicing agg err non ftl\n");

        //issue warm reset to clear fatal flag
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        csr_write_mpmc_halt();
    }
    else if (rst_count == 7) {
        VPRINTF(LOW, "-------------\nFW ftl/non-ftl err without mask\n---------------\n");
        lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_ERROR_FATAL, rand());
        lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_ERROR_NON_FATAL, rand());

        for(uint8_t i = 0; i < 10; i++);
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        csr_write_mpmc_halt();
    }
    else if (rst_count == 8) {
        VPRINTF(LOW, "-------------\nFW ftl/non-ftl err with mask\n---------------\n");
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTERNAL_FW_ERROR_FATAL_MASK, 0xffff);
        lsu_write_32(SOC_MCI_TOP_MCI_REG_INTERNAL_FW_ERROR_NON_FATAL_MASK, 0xffff);

        lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_ERROR_FATAL, rand());
        lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_ERROR_NON_FATAL, rand());

        for(uint8_t i = 0; i < 10; i++);
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        csr_write_mpmc_halt();
    } 
    else { //if (rst_count == 9) {
        VPRINTF(LOW, "-------------\nNotif0 conditions\n---------------\n");
        SEND_STDOUT_CTRL(TB_CMD_INJECT_NOTIF0);
        service_notif0_intr();

        // printf("Write to generic input wires 0\n");
        // lsu_write_32(SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_0, rand());
        // service_notif0_intr();

        // printf("Write to generic input wires 1\n");
        // lsu_write_32(SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_1, rand());
        // service_notif0_intr();
    // }
    // else {
        SEND_STDOUT_CTRL(0xFF);
        csr_write_mpmc_halt();
    }
}