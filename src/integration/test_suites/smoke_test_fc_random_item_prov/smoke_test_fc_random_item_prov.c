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

volatile char* stdout = (char *)0x21000410;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

#ifndef MY_RANDOM_SEED
#define MY_RANDOM_SEED 42
#endif // MY_RANDOM_SEED

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
 * Program a randomized fuse in `SW_MANUF_PARTITION`. The function consists
 * of the following steps:
 * 
 *   1. Write a value to a randomized fuse.
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
void program_sw_manuf_partition(void) {
    // Set AXI user ID to 1.
    uint32_t axi_conf;
    axi_conf = lsu_read_32(0x70000080);

    // 0x0D0: CPTRA_CORE_ANTI_ROLLBACK_DISABLE
    // 0x0D1: CPTRA_CORE_IDEVID_CERT_IDEVID_ATTR
    // 0x131: CPTRA_CORE_IDEVID_MANUF_HSM_IDENTIFIER
    // 0x141: CPTRA_CORE_SOC_STEPPING_ID
    // 0x143: CPTRA_SS_PROD_DEBUG_UNLOCK_PKS
    const uint32_t addresses[5] = {0x0D0, 0x0D1, 0x131, 0x141, 0x143};
    const uint32_t digest_address = 0x4F8;
    uint32_t fuse_address = addresses[2];

    const uint32_t data = 0xAB;
    uint32_t read_data;

    // Step 1
    dai_wr(fuse_address, data, 0, 32, 0);

    // Step 2
    dai_rd(fuse_address, &read_data, NULL, 32, 0);
    if (data != read_data) {
        VPRINTF(LOW, "ERROR: incorrect fuse data: expected: %08X actual: %08X\n", data, read_data);
        exit(1);
    }

    // Step 3
    dai_wr(digest_address, 0xFF, 0xFF, 64, 0);

    // Step 4
    reset_rtl();
    wait_dai_op_idle(0);

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
    digest[0] = lsu_read_32(FUSE_CTRL_SW_MANUF_PARTITION_DIGEST_0);
    digest[1] = lsu_read_32(FUSE_CTRL_SW_MANUF_PARTITION_DIGEST_1);
    if (digest[0] != 0xFF || digest[1] != 0xFF) {
        VPRINTF(LOW, "ERROR: digest is 0\n");
        exit(1);
    }

    VPRINTF(LOW, "DEBUG: program sw manuf successful\n");
}

/**
 * Program a randomized fuse in `VENDOR_SECRET_PROD_PARTITION`. The function consists
 * of the following steps:
 * 
 *   1. Write a value to a randomized fuse.
 *   2. Read back the value and verify it is equal to the value written in Step 1.
 *      This works as long as the secret partition has not been locked.
 *   3. Verify that the partition's digest register is 0.
 *   4. Lock the partition by calculating a hardware digest.
 *   5. Reset the RTL.
 *   6. Try to read the fuse and verify that it results in an error as the
 *      is secret and locked thus not accessible by software anymore.
 *   7. Try to write a value into the fuse and verify that it results in an error
 *      as the partition has been locked in Step 5.
 *   8. Read back the digest from the partition's digest register and verify it
 *      is non-zero.
 */
void program_vendor_secret_prod_partition() {
    // Set AXI user ID to 1.
    uint32_t axi_conf;
    axi_conf = lsu_read_32(0x70000080);

    const uint32_t base_address = 0x9D0;
    uint32_t fuse_address = base_address + 32*0;

    const uint32_t data[2] = {0xdeadbeef, 0xcafebabe};
    uint32_t read_data[2];

    // Step 1
    dai_wr(fuse_address, data[0], data[1], 64, 0);

    // Step 2
    dai_rd(fuse_address, &read_data[0], &read_data[1], 64, 0);
    if (data[0] != read_data[0] || data[1] != read_data[1]) {
        VPRINTF(LOW, "ERROR: incorrect fuse data: expected: %08X actual: %08X\n", data, read_data);
        exit(1);
    }

    // Step 3
    uint32_t digest[2];
    digest[0] = lsu_read_32(FUSE_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_0);
    digest[1] = lsu_read_32(FUSE_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_1);
    if (digest[0] != 0 || digest[1] != 0) {
        VPRINTF(LOW, "ERROR: digest is not 0\n");
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
    digest[0] = lsu_read_32(FUSE_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_0);
    digest[1] = lsu_read_32(FUSE_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_1);
    if (digest[0] == 0 && digest[1] == 0) {
        VPRINTF(LOW, "ERROR: digest is 0\n");
        exit(1);
    }

    VPRINTF(LOW, "DEBUG: program vendor secret prod successful\n");
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

    // TODO: This currently blocks the program execution.
    // srand((uint32_t)MY_RANDOM_SEED);

#ifdef PROGRAM_SECRET_PARTITON
    program_vendor_secret_prod_partition();
#else
    program_sw_manuf_partition();
#endif // PROGRAM_SECRET_PARTITION

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}