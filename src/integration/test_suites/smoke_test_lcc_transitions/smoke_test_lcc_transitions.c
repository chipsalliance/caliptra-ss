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

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    // Writing to Caliptra Boot GO register of MCI for CSS BootFSM to bring Caliptra out of reset 
    // This is just to see CSSBootFSM running correctly
    lsu_write_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, 1);
    VPRINTF(LOW, "MCU: Writing MCI SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO\n");

    uint32_t cptra_boot_go = lsu_read_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO);
    VPRINTF(LOW, "MCU: Reading SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO %x\n", cptra_boot_go);
    
    // Raw token for the state transition. Replace with the actual one.
    const uint32_t raw_token[4] = {
        0, 0, 0, 0
    };

    lcc_initialization();
    uint32_t lc_state = read_lc_state();
    uint32_t lc_counter = read_lc_counter();

    // Check if we need an unlock token.
    uint8_t use_token[] = {
        0, // from "no previous" to Raw
        1, // from Raw -> TestUnlocked0: real token
        0, // from TestUnlocked0 -> TestLocked0
        1, // ...
        0, // from TestUnlocked1 -> TestLocked1
        1,
        0, // from TestUnlocked2 -> TestLocked2
        1,
        0, // from TestUnlocked3 -> TestLocked3
        1,
        0, // from TestUnlocked4 -> TestLocked4
        1,
        0, // from TestUnlocked5 -> TestLocked5
        1,
        0, // from TestUnlocked6 -> TestLocked6
        1,
        1, // from TestUnlocked7 -> MANUF
        1, // from MANUF -> PROD
        1, // from PROD -> PROD_END
        0  // from PROD -> SCRAP
    };

    VPRINTF(LOW, "current_state %d next_state %d use_token %d\n", lc_state, lc_state + 1, use_token[lc_state + 1]);

    uint32_t next_lc_state_enc = encode_lc_state(lc_state + 1);
    sw_transition_req(next_lc_state_enc,
                              raw_token[0],
                              raw_token[1],
                              raw_token[2],
                              raw_token[3],
                              use_token[lc_state + 1]);

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
