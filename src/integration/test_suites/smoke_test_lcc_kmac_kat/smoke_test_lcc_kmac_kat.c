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

#define NUM_STATES 21

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    // Writing to Caliptra Boot GO register of MCI for CSS BootFSM to bring Caliptra out of reset 
    // This is just to see CSSBootFSM running correctly
    lsu_write_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, 1);
    VPRINTF(LOW, "MCU: Writing MCI SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO\n");

    uint32_t cptra_boot_go = lsu_read_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO);
    VPRINTF(LOW, "MCU: Reading SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO %x\n", cptra_boot_go);
    
    // Raw (unhashed) transition tokens.
    const uint32_t tokens[NUM_STATES][4] = {
        {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
        {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
        {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
        {0x7EBEA08B, 0x44593938, 0xB6F4A7E9, 0x16F6064B}, // CPTRA_SS_TEST_UNLOCK_TOKEN_0
        {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
        {0x8757DF07, 0x3FAC7019, 0x452ED1A3, 0x3C4353DC}, // CPTRA_SS_TEST_UNLOCK_TOKEN_1
        {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
        {0x7E9F2B57, 0x66696701, 0x352CFAAA, 0x4F005CE5}, // CPTRA_SS_TEST_UNLOCK_TOKEN_2
        {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
        {0x630BBA80, 0xF8C528CD, 0x0E4A5DCD, 0xC7050FC4}, // CPTRA_SS_TEST_UNLOCK_TOKEN_3
        {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
        {0xF2F130D7, 0xC5B2F9C0, 0xF254BBF6, 0x9D30EC03}, // CPTRA_SS_TEST_UNLOCK_TOKEN_4
        {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
        {0x71210A41, 0x56B5A675, 0xD535CDB7, 0x43272B5A}, // CPTRA_SS_TEST_UNLOCK_TOKEN_5
        {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
        {0xBD963661, 0xCB08EF49, 0x8ADEBE61, 0x830048CF}, // CPTRA_SS_TEST_UNLOCK_TOKEN_6
        {0x571D77F2, 0x1A14A21A, 0x60E3AE2A, 0x1EECAD58}, // CPTRA_SS_TEST_EXIT_TO_MANUF_TOKEN
        {0xCDD74C7A, 0x0408CDD4, 0x255AB47C, 0xFDA4DF39}, // CPTRA_SS_MANUF_TO_PROD_TOKEN
        {0x11DDBC6F, 0x2B2A890A, 0x6B49F203, 0xC0B77295}, // CPTRA_SS_PROD_TO_PROD_END_TOKEN
        {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
        {0x00000000, 0x00000000, 0x00000000, 0x00000000}  // empty
    };

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
