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
// Auto generated with the gen_fuse_ctrl_vmem script.
#include "smoke_test_lcc_kmac_kat.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

#define NUM_STATES 21

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
    uint32_t init_state = 2;

    if (lc_state_curr != state_sequence[init_state]) {
        VPRINTF(LOW, "ERROR: test expects to start in %d state!\n", init_state);
        exit(1);
    }

    for (uint32_t it = init_state; it < NUM_STATES - 3; it++) {
        uint32_t lc_state_next = state_sequence[it + 1];

        if (use_token[lc_state_next]) {
            VPRINTF(LOW, "INFO: Hashing token 0x%08x 0x%08x 0x%08x 0x%08x\n", tokens[lc_state_next][0], tokens[lc_state_next][1], tokens[lc_state_next][2], tokens[lc_state_next][3]);
        }

        transition_state(lc_state_next,
                     tokens[lc_state_next][0],
                     tokens[lc_state_next][1],
                     tokens[lc_state_next][2],
                     tokens[lc_state_next][3],
                     use_token[lc_state_next]);
        
        wait_dai_op_idle(0);

        lc_state_curr = read_lc_state();
        if (lc_state_curr != lc_state_next) {
            VPRINTF(LOW, "ERROR: incorrect state: exp: %d, act: %d\n", lc_state_next, lc_state_curr);
            exit(1);
        }

        if (use_token[lc_state_next]) {
            VPRINTF(LOW, "INFO: Token successfully hashed!\n");
        }
    }

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
