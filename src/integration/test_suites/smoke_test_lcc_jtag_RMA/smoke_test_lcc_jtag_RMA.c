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



void main (void)
{
    VPRINTF(LOW, "=================\nMCU: Caliptra Boot Go\n=================\n\n");    
    mcu_cptra_init_d(.cfg_skip_set_fuse_done=true);
    force_lcc_tokens();
    VPRINTF(LOW, "=========\nMCU: TESTING LCC STATE TRANS FROM ONE to RMA\n=================\n\n");   
    
    VPRINTF(LOW, "=================\n CALIPTRA_SS JTAG TEST with ROM \n=================\n\n");
    uint32_t lc_state_curr = read_lc_state();
    while (lc_state_curr != 21) {
        VPRINTF(LOW, "\nMCU: CALIPTRA_SS_LC_CTRL is in %d state!\n", lc_state_curr);
        VPRINTF(LOW, "\nMCU: CALIPTRA_SS_LC_CTRL is not in 1 state!\n");
        lc_state_curr = read_lc_state();
        for (uint16_t ii = 0; ii < 1000; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    }
    reset_fc_lcc_rtl();
    lc_state_curr = read_lc_state();
    for (uint16_t ii = 0; ii < 100; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);

}
