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

/**
 * Hashed token values. Can be calculated with the following script:
 *   from Crypto.Hash import cSHAKE128
 *   value = 0x0
 *   data = value.to_bytes(16, byteorder='little')
 *   custom = 'LC_CTRL'.encode('UTF-8')
 *   shake = cSHAKE128.new(data=data, custom=custom)
 *   digest = int.from_bytes(shake.read(16), byteorder='little')
 *   print(hex(digest))
 */
static uint32_t hashed_tokens[8][4] = {
    { 0x6db9058d, 0xd5c1d25f, 0xaecf5ff1, 0x3852305b }, // value = 0
    { 0xe65e577c, 0x542f2d2d, 0x73f29e7b, 0xee4fe51a }, // value = 1
    { 0x776a6ed3, 0xac7f4d2a, 0x31bafcef, 0x365671d1 }, // value = 2
    { 0xdcbc2b7f, 0x0f86ccda, 0xa66340c7, 0x56228106 }, // value = 3
    { 0x5ad76df9, 0x8756e714, 0x04f2f7fc, 0x97045d52 }, // value = 4
    { 0x83fedf4e, 0xab931943, 0xeaa495ce, 0x1af9ead2 }, // value = 5
    { 0xe2ad2527, 0x5d416692, 0xe0d874a3, 0xf0113a15 }, // value = 6
    { 0x536a2f30, 0xf47b04d1, 0x2cf01443, 0xf0113a15 }  // value = 7
};

/**
 * This function steps through all the test unlock/lock states starting
 * from TEST_UNLOCKED0. Before that all unlock tokens are written into
 * their corresponding fuses in the SECRET_LC_TRANSITION_PARTITION
 * partition which is then locked by computing the hardware digest.
 * Note this is a routine with a long running time.
 */
void iterate_test_unlock_states() {
    // Set AXI user ID to 1.
    uint32_t axi_conf;
    axi_conf = lsu_read_32(0x70000080);

    // 0x500: CPTRA_SS_TEST_UNLOCK_TOKEN_0
    const uint32_t base_address = 0x500;

    // Write the tokens into the partition.
    for (uint32_t i = 0; i < 8; i++) {
        dai_wr(base_address + 0x10*i, hashed_tokens[i][0], hashed_tokens[i][1], 64, 0);
        dai_wr(base_address + 0x08 + 0x10*i, hashed_tokens[i][2], hashed_tokens[i][3], 64, 0);
    }

    calculate_digest(base_address);

    reset_rtl();
    wait_dai_op_idle(0);

    for (uint32_t state = TEST_LOCKED0, token = 0x0; state <= TEST_UNLOCKED7; token += (state & 0x1), state++) {
        VPRINTF(LOW, "LC_CTRL: transition to %d state\n", state);

        transition_state(state, token, 0, 0, 0, state & 0x1 /* No token required for TEST_LOCKED states*/ );
        wait_dai_op_idle(0);

        uint32_t act_state = lsu_read_32(LC_CTRL_LC_STATE_OFFSET);
        uint32_t exp_state = calc_lc_state_mnemonic(state);
        if (act_state != exp_state) {
            VPRINTF(LOW, "ERROR: incorrect state: exp: %08X, act: %08X\n", act_state, exp_state);
            exit(1);
        }
    }
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
    
    transition_state(TEST_UNLOCKED0, raw_unlock_token[0], raw_unlock_token[1], raw_unlock_token[2], raw_unlock_token[3], 1);
    wait_dai_op_idle(0);
    
    initialize_otp_controller();

    iterate_test_unlock_states();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}

// #include <string.h>
// #include <stdint.h>
// #include <time.h>
// #include <stdlib.h>

// #include "soc_address_map.h"
// #include "printf.h"
// #include "riscv_hw_if.h"
// #include "soc_ifc.h"
// #include "fuse_ctrl_address_map.h"
// #include "caliptra_ss_lc_ctrl_address_map.h"
// #include "caliptra_ss_lib.h"
// #include "fuse_ctrl.h"
// #include "lc_ctrl.h"

// volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
// #ifdef CPT_VERBOSITY
//     enum printf_verbosity verbosity_g = CPT_VERBOSITY;
// #else
//     enum printf_verbosity verbosity_g = LOW;
// #endif

// /**
//  * Most register accesses are covered by the other smoke tests. Here,
//  * we check that reads to the various error registers are correct and
//  * verify whether the read lock register actually locks a partition.
//  * The test proceeds in the following steps:
//  *
//  *  1. Read out all the error registers.
//  *  2. Write a value to a fuse in a software partition.
//  *  3. Read back the same fuse and verify that the data is equal to
//  *     the value written in Step 2.
//  *  4. Clear the read enable bit in the partition's read lock register.
//  *  5. Check that a read now results in an error.
//  */
// void xxx() {
//     // Set AXI user ID to 1.
//     uint32_t axi_conf;
//     axi_conf = lsu_read_32(0x70000080);

//     // 0x950: CPTRA_CORE_ECC_REVOCATION_0
//     const uint32_t fuse_address = 0x950;

//     const uint32_t data = 0xdeaddead;
//     uint32_t read_data;

//     // Step 1
//     for (int i = 0; i < 18; i++) {
//         if (lsu_read_32(FUSE_CTRL_ERR_CODE_0+0x4*i)) {
//             VPRINTF(LOW, "ERROR: err register %d is not zero\n", i);
//             exit(1);
//         }
//     }

//     // Step 2
//     dai_wr(fuse_address, data, 0, 32, 0);

//     // Step 3
//     dai_rd(fuse_address, &read_data, NULL, 32, 0);

//     // Step 4
//     lsu_write_32(FUSE_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK, 0);

//     // Step 5
//     dai_rd(fuse_address, &read_data, NULL, 32, FUSE_CTRL_STATUS_DAI_ERROR_MASK);
// }

// void main (void) {
//     VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
//     // Writing to Caliptra Boot GO register of MCI for CSS BootFSM to bring Caliptra out of reset 
//     // This is just to see CSSBootFSM running correctly
//     lsu_write_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, 1);
//     VPRINTF(LOW, "MCU: Writing MCI SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO\n");

//     uint32_t cptra_boot_go = lsu_read_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO);
//     VPRINTF(LOW, "MCU: Reading SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO %x\n", cptra_boot_go);
      
//     lcc_initialization();

//     transition_state(TEST_UNLOCKED0, raw_unlock_token[0], raw_unlock_token[1], raw_unlock_token[2], raw_unlock_token[3], 1);
//     wait_dai_op_idle(0);

//     initialize_otp_controller();

//     xxx();

//     for (uint8_t ii = 0; ii < 160; ii++) {
//         __asm__ volatile ("nop"); // Sleep loop as "nop"
//     }

//     SEND_STDOUT_CTRL(0xff);
// }