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

// Auto generated with the gen_fuse_ctrl_vmem.py script
#include "caliptra_ss_lcc_st_trans.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    // Writing to Caliptra Boot GO register of MCI for CSS BootFSM to bring Caliptra out of reset 
    // This is just to see CSSBootFSM running correctly
    lsu_write_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, 1);
    VPRINTF(LOW, "MCU: Writing MCI SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO\n");

    uint32_t cptra_boot_go = lsu_read_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO);
    VPRINTF(LOW, "MCU: Reading SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO %x\n", cptra_boot_go);

    lcc_initialization();
    uint32_t lc_state_curr = read_lc_state();
    uint32_t lc_state_next = state_sequence[lc_state_curr + 1];
    uint32_t lc_cnt_curr = read_lc_counter();
    uint32_t lc_cnt_next = lc_cnt_curr + 1;

    VPRINTF(LOW, "current_state %d next_state %d use_token %d\n", lc_state_curr, lc_state_next, use_token[lc_state_next]);

    if (lc_state_next == 20) {
        // Transition to SCRAP require setting the PPD pin.
        force_PPD_pin();
    }
    transition_state(lc_state_next,
                     tokens[lc_state_next][0],
                     tokens[lc_state_next][1],
                     tokens[lc_state_next][2],
                     tokens[lc_state_next][3],
                     use_token[lc_state_next]);

    wait_dai_op_idle(0);

    // Check if we have reached the counter limit.
    // State transition will then fail.
    uint32_t lc_state_exp = lc_state_next;
    if (lc_cnt_curr == 24) {
        VPRINTF(LOW, "Info: Reach LC_CNT limit, state transition not allowed.\n");
        lc_state_exp = lc_state_curr;
    }

    lc_state_curr = read_lc_state();
    if (lc_state_curr != lc_state_exp) {
        VPRINTF(LOW, "ERROR: incorrect state: exp: %d, act: %d\n", lc_state_exp, lc_state_curr);
        exit(1);
    }

    VPRINTF(LOW, "In state: %d, as expected\n", lc_state_curr);

    uint32_t lc_cnt_exp = lc_cnt_next;
    if (lc_cnt_curr == 24) {
        VPRINTF(LOW, "Info: Reach LC_CNT limit, counter does not increment any more.\n");
        lc_cnt_exp = lc_cnt_curr;
    }

    lc_cnt_curr = read_lc_counter();
    if (lc_cnt_curr != lc_cnt_exp) {
        VPRINTF(LOW, "ERROR: incorrect counter: exp: %d, act: %d\n", lc_cnt_exp, lc_cnt_curr);
        exit(1);
    }

    VPRINTF(LOW, "Counter: %d, as expected\n", lc_cnt_curr);

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
