#include <string.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
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

void external_clock() {
    const uint32_t claim_trans_val = 0x96;

    const uint32_t freqs[4] = {
        CMD_FC_LCC_EXT_CLK_500MHZ,
        CMD_FC_LCC_EXT_CLK_160MHZ,
        CMD_FC_LCC_EXT_CLK_400MHZ,
        CMD_FC_LCC_EXT_CLK_1000MHZ
    };

    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, freqs[xorshift32() % 4]);

    uint32_t reg_value, loop_ctrl;
    while (loop_ctrl != claim_trans_val) {
        lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, claim_trans_val);
        reg_value = lsu_read_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET);
        loop_ctrl = reg_value & claim_trans_val;
    }

    lsu_write_32(LC_CTRL_TRANSITION_CTRL_OFFSET, 0x1);
    wait_dai_op_idle(0);

    grant_caliptra_core_for_fc_writes();

    dai_wr(0x000, 0xFF, 0xFF, 64, 0);
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

    external_clock();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
