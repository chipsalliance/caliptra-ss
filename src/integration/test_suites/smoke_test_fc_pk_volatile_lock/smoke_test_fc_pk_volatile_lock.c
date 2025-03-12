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
#include "fuse_ctrl.h"
#include "lc_ctrl.h"

volatile char* stdout = (char *)0x21000410;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void raw_to_testunlock0(){
    uint32_t reg_value;
    uint32_t status_val;
    uint32_t loop_ctrl;

    uint32_t next_lc_state = 0x1; // TEST_UNLOCKED0
    uint32_t next_lc_state_5bit = next_lc_state & 0x1F; // Extract 5-bit value (DecLcStateWidth = 5)
    uint32_t targeted_state_5 = 
        (next_lc_state_5bit << 25) | 
        (next_lc_state_5bit << 20) | 
        (next_lc_state_5bit << 15) | 
        (next_lc_state_5bit << 10) | 
        (next_lc_state_5bit << 5)  | 
        next_lc_state_5bit;

    sw_transition_req(targeted_state_5, 0xf12a5911, 0x421748a2, 0xadfc9693, 0xef1fadea, 1); //TEST_UNLOCKED0, tokenmsb, tokenlsb, conditional

    reg_value = lsu_read_32(LC_CTRL_HW_REVISION0_OFFSET); // Reset the lcc and its bfm
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is under reset!\n");
    for (uint8_t ii = 0; ii < 16; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is in TEST_UNLOCK0 state!\n");
}

/**
 * Program two fuses in `VENDOR_HASHES_PROD_PARTITION`, then verify whether
 * the volatile lock works as intended. The test proceeds in the following steps:
 * 
 *   1. Write a value to first fuse.
 *   2. Write a value to second fuse.
 *   3. Activate the volatile lock such that the fuse from step 2 is now in the
 *      locked region.
 *   4. Verify that writing to the second fuse now results in an error.
 */
void program_vendor_hashes_prod_partition(void) {
    // Set AXI user ID to 1.
    uint32_t axi_conf;
    axi_conf = lsu_read_32(0x70000080);

    // 0x6C2: CPTRA_CORE_VENDOR_PK_HASH_3
    // 0x724: CPTRA_CORE_VENDOR_PK_HASH_5
    const uint32_t addresses[2] = {0x6C2, 0x724};

    const uint32_t data = 0xdeadbeef;

    // Step 1
    dai_wr(addresses[0], data, 0, 32, 0);

    // Step 2
    dai_wr(addresses[1], data+1, 0, 32, 0);

    // Step 3
    lsu_write_32(FUSE_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK, 4); // Lock all hashes starting from index 5.

    // Step 4
    dai_wr(addresses[1], data+2, 0, 32, FUSE_CTRL_STATUS_DAI_ERROR_MASK);
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    // Writing to Caliptra Boot GO register of MCI for CSS BootFSM to bring Caliptra out of reset 
    // This is just to see CSSBootFSM running correctly
    lsu_write_32(SOC_MCI_REG_CALIPTRA_BOOT_GO, 1);
    VPRINTF(LOW, "MCU: Writing MCI SOC_MCI_REG_CALIPTRA_BOOT_GO\n");

    uint32_t cptra_boot_go = lsu_read_32(SOC_MCI_REG_CALIPTRA_BOOT_GO);
    VPRINTF(LOW, "MCU: Reading SOC_MCI_REG_CALIPTRA_BOOT_GO %x\n", cptra_boot_go);
    
    lcc_initialization();    
    raw_to_testunlock0();
    initialize_otp_controller();

    //srand((uint32_t)MY_RANDOM_SEED);

    program_vendor_hashes_prod_partition();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}