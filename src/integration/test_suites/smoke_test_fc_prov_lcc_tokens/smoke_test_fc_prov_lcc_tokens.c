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

void calculate_digest(uint32_t partition_base_address) {
    // Step 1: Check if DAI is idle
    wait_dai_op_idle(0);

    // Step 2: Write the partition base address to DIRECT_ACCESS_ADDRESS
    lsu_write_32(FUSE_CTRL_DIRECT_ACCESS_ADDRESS, partition_base_address);
    VPRINTF(LOW, "INFO: Partition base address 0x%08X written to DIRECT_ACCESS_ADDRESS.\n", partition_base_address);

    // Step 3: Trigger a digest calculation command
    lsu_write_32(FUSE_CTRL_DIRECT_ACCESS_CMD, 0x4);

    // Step 4: Poll STATUS until DAI state goes back to idle    
    wait_dai_op_idle(0);
    return;
}

/**
 * Program a LCC transition token in `SECRET_LC_TRANSITION_PARTITION` and verify
 * that the valid bit is asserted once the partition has been locked. The test
 * proceeds in the following steps:
 * 
 *   1. Write a full transition token into the partition.
 *   2. Read back the token and verify it is equal to the token written in Step 1.
 *      This works as long as the secret partition has not been locked.
 *   3. Verify that the partition's digest register is 0.
 *   4. Lock the partition by calculating a hardware digest.
 *   5. Reset the RTL.
 *   6. Try to read the token and verify that it results in an error as the
 *      partition is secret and locked, thus not accessible by software anymore.
 *   7. Try to write a value into the partition and verify that it results in an error
 *      as the partition has been locked in Step 5.
 *   8. Read back the digest from the partition's digest register and verify it
 *      is non-zero.
 *   9. Use a backdoor channel to verify that the valid bit is set.
 */
void program_secret_lc_transition_partition() {
    // Set AXI user ID to 1.
    uint32_t axi_conf;
    axi_conf = lsu_read_32(0x70000080);

    // 0x500: CPTRA_SS_TEST_EXIT_TO_MANUF_TOKEN
    const uint32_t base_address = 0x500;
    const uint32_t fuse_address = 0x580;

    const uint32_t data[4] = {0xdeadbeef, 0xcafebabe, 0x12345678, 0xabababab};
    uint32_t read_data[4];

    // Step 1
    dai_wr(fuse_address, data[0], data[1], 64, 0);
    dai_wr(fuse_address+8, data[2], data[3], 64, 0);

    // Step 2
    dai_rd(fuse_address, &read_data[0], &read_data[1], 64, 0);
    dai_rd(fuse_address+8, &read_data[2], &read_data[3], 64, 0);
    if (memcmp(data, read_data, 16)) {
        VPRINTF(LOW, "ERROR: incorrect fuse data: expected: %08X actual: %08X\n", data[2], read_data[2]);
        exit(1);
    }

    // Step 3
    uint32_t digest[2];
    digest[0] = lsu_read_32(FUSE_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_0);
    digest[1] = lsu_read_32(FUSE_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_1);
    if (digest[0] != 0 || digest[1] != 0) {
        VPRINTF(LOW, "ERROR: digest is not 0\n");
        exit(1);
    }

    // Step 4
    calculate_digest(base_address);

    // Step 5
    reset_rtl();

    // Step 6
    dai_rd(fuse_address, &read_data[0], &read_data[1], 64, FUSE_CTRL_STATUS_DAI_ERROR_MASK);

    // Step 7
    dai_wr(fuse_address, data[0], data[1], 64, FUSE_CTRL_STATUS_DAI_ERROR_MASK);

    // Step 8
    digest[0] = lsu_read_32(FUSE_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_0);
    digest[1] = lsu_read_32(FUSE_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_1);
    if (digest[0] == 0 && digest[1] == 0) {
        VPRINTF(LOW, "ERROR: digest is 0\n");
        exit(1);
    }

    // Step 9
    // Use backdoor channel to verify that the valid bit is set.
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

    program_secret_lc_transition_partition();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}