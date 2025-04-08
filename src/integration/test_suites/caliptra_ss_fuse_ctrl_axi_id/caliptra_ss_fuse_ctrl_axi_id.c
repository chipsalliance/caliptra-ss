#include <string.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "fuse_ctrl_address_map.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

/**
 * This test performs DAI writes over the AXI bus on the boundaries of the
 * fuse controller access table entries.
 */
void axi_id() {
    const uint32_t sentinel = 0xAB;
    const uint32_t granularity = 64;

    // Both CPTRA_CORE_MANUF_DEBUG_UNLOCK_TOKEN and CPTRA_CORE_UDS_SEED must not
    // be modified by the AXI requests stemming from the MCU.
    grant_mcu_for_fc_writes(); 
    dai_wr(0x000, sentinel, sentinel, granularity, FUSE_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(0x048, sentinel, sentinel, granularity, FUSE_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(0x090, sentinel, sentinel, granularity, 0 /* Should work */);

    // All fuses should be writable by the Caliptra core.
    grant_caliptra_core_for_fc_writes();
    dai_wr(0x000, sentinel, sentinel, granularity, 0);
    dai_wr(0x048, sentinel, sentinel, granularity, 0);
    dai_wr(0x090, sentinel, sentinel, granularity, 0);
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    transition_state(TEST_UNLOCKED0, raw_unlock_token[0], raw_unlock_token[1], raw_unlock_token[2], raw_unlock_token[3], 1);
    wait_dai_op_idle(0);

    initialize_otp_controller();

    axi_id();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
