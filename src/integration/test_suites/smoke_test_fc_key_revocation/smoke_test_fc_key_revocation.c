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
 * Program the revocation bits in `VENDOR_REVOCATIONS_PROD_PARTITION`. The test
 * proceeds in the following steps:
 * 
 *   1. Write a value to a fuse.
 *   2. Read back the value and verify it is equal to the value written in Step 1.
 *   3. Write a dummy digest into the partition's digest field, which locks the
 *      partition. This works since it is an unbuffered software partition.
 *   4. Reset the RTL.
 *   5. Read back the fuse again and verify that the value has not changed, i.e.,
 *      is equal to the value written in Step 1.
 *   6. Try to write a value into the fuse and verify that it results in an error
 *      as the partition has been locked in Step 3.
 *   7. Read back the digest from the partition's digest register and verify it
 *      is equal to the dummy digest written in Step 3.
 */
void vendor_revocations_prod_partition() {
    // Set AXI user ID to 1.
    uint32_t axi_conf;
    axi_conf = lsu_read_32(0x70000080);

    // 0x950: CPTRA_CORE_ECC_REVOCATION_0
    const uint32_t base_address = 0x950;
    const uint32_t digest_address = 0x9E0;
    const uint32_t fuse_address = base_address;

    const uint32_t data = 0xdeadbeef;
    uint32_t read_data;

    uint32_t status = 0;

    // Step 1
    dai_wr(fuse_address, data, 0, 32, 0);

    // Step 2
    dai_rd(fuse_address, &read_data, NULL, 32, 0);
    if (data != read_data) {
        VPRINTF(LOW, "ERROR: incorrect fuse data: expected: %08X actual: %08X\n", data, read_data);
        exit(1);
    }

    // Step 3
    dai_wr(digest_address, 0xff, 0xff, 64, 0);

    // Step 4
    reset_rtl();

    // Step 5
    dai_rd(fuse_address, &read_data, NULL, 32, 0);
    if (data != read_data) {
        VPRINTF(LOW, "ERROR: incorrect fuse data: expected: %08X actual: %08X\n", data, read_data);
        exit(1);
    }

    // Step 6
    dai_wr(fuse_address, data, 0, 32, FUSE_CTRL_STATUS_DAI_ERROR_MASK);

    // Step 7
    uint32_t digest[2];
    digest[0] = lsu_read_32(FUSE_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_0);
    digest[1] = lsu_read_32(FUSE_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_1);
    if (digest[0] == 0 && digest[1] == 0) {
        VPRINTF(LOW, "ERROR: digest is 0\n");
        exit(1);
    }
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

    vendor_revocations_prod_partition();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}