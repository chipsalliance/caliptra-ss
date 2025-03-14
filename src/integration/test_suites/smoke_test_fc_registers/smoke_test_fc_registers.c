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
 * Most register accesses are covered by the other smoke tests. Here,
 * we check that reads to the various error registers are correct and
 * verify whether the read lock register actually locks a partition.
 * The test proceeds in the following steps:
 *
 *  1. Read out all the error registers.
 *  2. Write a value to a fuse in a software partition.
 *  3. Read back the same fuse and verify that the data is equal to
 *     the value written in Step 2.
 *  4. Clear the read enable bit in the partition's read lock register.
 *  5. Check that a read now results in an error.
 */
void register_accesses() {
    // Set AXI user ID to 1.
    uint32_t axi_conf;
    axi_conf = lsu_read_32(0x70000080);

    // 0x950: CPTRA_CORE_ECC_REVOCATION_0
    const uint32_t fuse_address = 0x950;

    const uint32_t data = 0xdeadbeef;
    uint32_t read_data;

    // Step 1
    for (int i = 0; i < 18; i++) {
        if (lsu_read_32(FUSE_CTRL_ERR_CODE_0+0x4*i)) {
            VPRINTF(LOW, "ERROR: err register %d is not zero\n", i);
            exit(1);
        }
    }

    // Step 2
    dai_wr(fuse_address, data, 0, 32, 0);

    // Step 3
    dai_rd(fuse_address, &read_data, NULL, 32, 0);

    // Step 4
    lsu_write_32(FUSE_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK, 0);

    // Step 5
    dai_rd(fuse_address, &read_data, NULL, 32, FUSE_CTRL_STATUS_DAI_ERROR_MASK);
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    // Writing to Caliptra Boot GO register of MCI for CSS BootFSM to bring Caliptra out of reset 
    // This is just to see CSSBootFSM running correctly
    lsu_write_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, 1);
    VPRINTF(LOW, "MCU: Writing MCI SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO\n");

    uint32_t cptra_boot_go = lsu_read_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO);
    VPRINTF(LOW, "MCU: Reading SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO %x\n", cptra_boot_go);
    
    lcc_initialization();    
    raw_to_testunlock0();
    initialize_otp_controller();

    register_accesses();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
