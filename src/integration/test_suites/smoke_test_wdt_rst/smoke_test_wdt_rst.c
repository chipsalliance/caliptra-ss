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
#include "wdt.h"
#include "caliptra_ss_lib.h"
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

volatile uint32_t * wdt_timer1_en       = (uint32_t *) SOC_MCI_TOP_MCI_REG_WDT_TIMER1_EN;
volatile uint32_t * wdt_timer1_ctrl     = (uint32_t *) SOC_MCI_TOP_MCI_REG_WDT_TIMER1_CTRL;
volatile uint32_t * wdt_timer1_period_0 = (uint32_t *) SOC_MCI_TOP_MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_0;
volatile uint32_t * wdt_timer1_period_1 = (uint32_t *) SOC_MCI_TOP_MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_1;
volatile uint32_t * soc_intr_en         = (uint32_t *) SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R; //TODO: confirm
volatile uint32_t * mci_global_intr_en  = (uint32_t *) SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R;

volatile uint32_t * wdt_timer2_en       = (uint32_t *) SOC_MCI_TOP_MCI_REG_WDT_TIMER2_EN;
volatile uint32_t * wdt_timer2_ctrl     = (uint32_t *) SOC_MCI_TOP_MCI_REG_WDT_TIMER2_CTRL;
volatile uint32_t * wdt_timer2_period_0 = (uint32_t *) SOC_MCI_TOP_MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_0;
volatile uint32_t * wdt_timer2_period_1 = (uint32_t *) SOC_MCI_TOP_MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_1;

volatile uint32_t * hw_error_fatal      = (uint32_t *) SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void nmi_handler (void);

void nmi_handler (void) {
    VPRINTF(LOW, "*** Entering NMI Handler ***\n");
    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL) & MCI_REG_HW_ERROR_FATAL_NMI_PIN_MASK) {
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);
        csr_write_mpmc_halt();
    }
    else {
        VPRINTF(ERROR, "Unexpected entry into NMI handler function\n");
    }
}

void main(void) {
    VPRINTF(LOW, "---------------------------\n");
    VPRINTF(LOW, " WDT Smoke Test with reset\n");
    VPRINTF(LOW, "---------------------------\n");

    //Enable SOC notif interrupt
    *soc_intr_en = MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_MASK | MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_MASK;
    *mci_global_intr_en = MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK | MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK;
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR, (uint32_t) (nmi_handler));
    //Call interrupt init
    // init_interrupts(); //TODO
    

    rst_count++;
    VPRINTF(LOW, "----------------\nrst count = %d\n----------------\n", rst_count);

    if (rst_count == 1) {
        VPRINTF(LOW, "Cascaded mode, t1 timeout, warm rst\n");
        configure_wdt_cascade(0x200, 0x00, 0xffffffff, 0xffffffff);
        
        VPRINTF(LOW, "Stall until timer1 times out\n");
        service_t1_intr();
        
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        csr_write_mpmc_halt();
    }
    else if (rst_count == 2) {
        VPRINTF(LOW, "Cascaded mode, t1 timeout, cold rst\n");
        configure_wdt_cascade(0x200, 0x00, 0xffffffff, 0xffffffff);

        *wdt_timer1_ctrl = MCI_REG_WDT_TIMER1_CTRL_TIMER1_RESTART_MASK;

        service_t1_intr();
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);
        csr_write_mpmc_halt();
    }
    else if (rst_count == 3) {
        VPRINTF(LOW, "Independent mode - both timers enabled - warm rst\n");
        configure_wdt_independent(BOTH_TIMERS_EN, 0x200, 0x00000000, 0x200, 0x00000000);
        
        VPRINTF(LOW, "Stall until timer1 times out\n");
        service_t1_intr();
        //reset t1
        *wdt_timer1_en = 0;
        
        VPRINTF(LOW, "Stall until timer1 times out\n");
        service_t2_intr();
        //reset t2
        *wdt_timer2_en = 0;
        
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        csr_write_mpmc_halt();
    }
    else if (rst_count == 4) {
        VPRINTF(LOW, "Independent mode - both timers enabled - cold rst\n");
        configure_wdt_independent(BOTH_TIMERS_EN, 0x200, 0x00000000, 0x200, 0x00000000);
    
        VPRINTF(LOW, "Stall until timer1 times out\n");
        service_t1_intr();
        *wdt_timer1_en = 0;

        VPRINTF(LOW, "Stall until timer2 times out\n");
        service_t2_intr();
        *wdt_timer2_en = 0;
        
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);
        csr_write_mpmc_halt();
    }
    else if (rst_count == 5) {
        VPRINTF(LOW, "Cascaded mode with timer2 timeout - NMI - cold rst\n");
        configure_wdt_cascade(0x200, 0x00, 0x00000200, 0x00000000);

        VPRINTF(LOW, "Stall until timer1 times out\n");
        VPRINTF(LOW, "Stall until timer2 times out\n");

        while(!(lsu_read_32(SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL) & MCI_REG_HW_ERROR_FATAL_NMI_PIN_MASK));
        handle_error("WDT timeout in cascade mode is expected to trigger NMI and reset!\n");
    }
    else if (rst_count == 6) {
        if ((*hw_error_fatal && MCI_REG_HW_ERROR_FATAL_NMI_PIN_MASK) == 1) {
            VPRINTF(ERROR, "Cold rst should have reset hw_fatal_error nmi_pin!\n");
            SEND_STDOUT_CTRL(0x1);
        }

        VPRINTF(LOW, "Independent mode - timer2 enabled, timer1 disabled - warm rst\n");
        *wdt_timer2_en = MCI_REG_WDT_TIMER2_EN_TIMER2_EN_MASK;
        set_t2_period(0x00000200, 0x00000000);
        
        VPRINTF(LOW, "Stall until timer2 times out\n");
        service_t2_intr();
        *wdt_timer2_en = 0;
        
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        csr_write_mpmc_halt();
    }
    else if (rst_count == 7) {
        VPRINTF(LOW, "Independent mode - timer2 enabled, timer1 disabled - cold rst\n");
        configure_wdt_independent(T1_DIS_T2_EN, 0x200, 0x00000000, 0x200, 0x00000000);
        
        VPRINTF(LOW, "Stall until timer2 times out\n");
        service_t2_intr();
        *wdt_timer2_en = 0;
        
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);
        csr_write_mpmc_halt();
    }
    else if (rst_count == 8) {
        //Issue warm reset during WDT operation
        //WDT cascade mode
        VPRINTF(LOW, "Cascade mode with warm reset during operation\n");
        configure_wdt_cascade(0x37, 0x00, 0xffffffff, 0xffffffff);
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        csr_write_mpmc_halt();
    }
    else if (rst_count == 9) {
        //Issue cold reset during WDT operation
        VPRINTF(LOW, "Cascade mode with cold reset during operation\n");
        configure_wdt_cascade(0x37, 0x00, 0xffffffff, 0xffffffff);
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);
        csr_write_mpmc_halt();
    }
    else if (rst_count == 10) {
        //Issue warm reset during WDT operation
        //WDT cascade mode
        VPRINTF(LOW, "Independent mode with warm reset during operation\n");
        configure_wdt_independent(BOTH_TIMERS_EN, 0x200, 0x00000000, 0x34, 0x00000000);
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        csr_write_mpmc_halt();
    }
    else if (rst_count == 11) {
        //Issue warm reset during WDT operation
        //WDT cascade mode
        VPRINTF(LOW, "Independent mode with cold reset during operation\n");
        configure_wdt_independent(BOTH_TIMERS_EN, 0x200, 0x00000000, 0x34, 0x00000000);
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);
        csr_write_mpmc_halt();
    }
    else if (rst_count == 12) {
        //Issue warm reset during WDT operation
        //WDT cascade mode
        VPRINTF(LOW, "Independent mode - t2 en with warm reset during operation\n");
        configure_wdt_independent(T1_DIS_T2_EN, 0x200, 0x00000000, 0x200, 0x00000000);
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        csr_write_mpmc_halt();
    }
    else if (rst_count == 13) {
        //Issue warm reset during WDT operation
        //WDT cascade mode
        VPRINTF(LOW, "Independent mode - t2 en with cold reset during operation\n");
        configure_wdt_independent(T1_DIS_T2_EN, 0x200, 0x00000000, 0x200, 0x00000000);
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);
        csr_write_mpmc_halt();
    }
    else {
        SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
        csr_write_mpmc_halt();
    }
}


