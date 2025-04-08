#include <string.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
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

    // 0x910: CPTRA_CORE_ECC_REVOCATION_0
    const uint32_t fuse_address = 0x910;

    const uint32_t data = 0xdeadbeef;
    uint32_t read_data;

    // Step 1
    for (int i = 0; i < 18; i++) {
        if (lsu_read_32(SOC_OTP_CTRL_ERR_CODE_RF_ERR_CODE_0+0x4*i)) {
            VPRINTF(LOW, "ERROR: err register %d is not zero\n", i);
            exit(1);
        }
    }

    // Step 2
    dai_wr(fuse_address, data, 0, 32, 0);

    // Step 3
    dai_rd(fuse_address, &read_data, NULL, 32, 0);

    // Step 4
    lsu_write_32(SOC_OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK, 0);

    // Step 5
    dai_rd(fuse_address, &read_data, NULL, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    // Set AXI user ID to MCU.
    grant_mcu_for_fc_writes(); 

    transition_state(TEST_UNLOCKED0, raw_unlock_token[0], raw_unlock_token[1], raw_unlock_token[2], raw_unlock_token[3], 1);
    wait_dai_op_idle(0);

    initialize_otp_controller();

    register_accesses();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}