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
        SEND_STDOUT_CTRL(0xf6);
    }
    else {
        VPRINTF(ERROR, "Unexpected entry into NMI handler function\n");
    }
}

void main(void) {
    VPRINTF(LOW, "---------------------------\n");
    VPRINTF(LOW, " WDT Smoke Test\n");
    VPRINTF(LOW, "---------------------------\n");

    //Enable SOC notif interrupt
    *soc_intr_en = MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_MASK | MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_MASK;
    *mci_global_intr_en = MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK | MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK;
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR, (uint32_t) (nmi_handler));
    //Call interrupt init
    // init_interrupts(); //TODO
    

    rst_count++;

    if (rst_count == 1) {
        VPRINTF(LOW, "Cascade mode\n");
        lsu_write_32(SOC_MCI_TOP_MCI_REG_WDT_TIMER2_EN, 0x0);
        configure_wdt_cascade(0x00000040, 0x00000000, 0x00000000, 0x00000001);

        while (!(lsu_read_32(SOC_MCI_TOP_MCI_REG_WDT_STATUS) & MCI_REG_WDT_STATUS_T1_TIMEOUT_MASK));
        VPRINTF(LOW, "WDT T1 timed out as expected\n");

        service_t1_intr();

        VPRINTF(LOW, "Independent mode\n");
        configure_wdt_independent(BOTH_TIMERS_EN, 0x00000040, 0x00000000, 0x00000040, 0x00000000);

        VPRINTF(LOW, "Reading wdt status reg\n");
        while (!(lsu_read_32(SOC_MCI_TOP_MCI_REG_WDT_STATUS) & MCI_REG_WDT_STATUS_T1_TIMEOUT_MASK));
        VPRINTF(LOW, "WDT T1 timed out as expected\n");
        while (!(lsu_read_32(SOC_MCI_TOP_MCI_REG_WDT_STATUS) & MCI_REG_WDT_STATUS_T2_TIMEOUT_MASK));
        VPRINTF(LOW, "WDT T2 timed out as expected\n");

        service_t1_intr();
        service_t2_intr();

        
        set_default_t1_period();
        set_default_t2_period();
        configure_wdt_independent(BOTH_TIMERS_DIS, 0x00000000, 0x00000000, 0x00000000, 0x00000000);

        VPRINTF(LOW, "Cascade mode with t2 timeout\n");
        configure_wdt_cascade(0x00000040, 0x00000000, 0x00000040, 0x00000000);

        VPRINTF(LOW, "Reading wdt status reg\n");
        while (!(lsu_read_32(SOC_MCI_TOP_MCI_REG_WDT_STATUS) & MCI_REG_WDT_STATUS_T1_TIMEOUT_MASK));
        VPRINTF(LOW, "WDT T1 timed out as expected\n");
        while (!(lsu_read_32(SOC_MCI_TOP_MCI_REG_WDT_STATUS) & MCI_REG_WDT_STATUS_T2_TIMEOUT_MASK));
        VPRINTF(LOW, "WDT T2 timed out as expected\n");

    }
    else if (rst_count == 2) {
        VPRINTF(LOW, "Coming out of warm reset after NMI intr\n");
    }

    SEND_STDOUT_CTRL(0x00);
    SEND_STDOUT_CTRL(0xff);
}


