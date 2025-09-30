//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
//
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//********************************************************************************
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
#include "fuse_ctrl_mmap.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void secret_with_shuffled_ops_with_fail(void) {
    uint32_t data0 = 0xA5A5A5A5;
    uint32_t data1 = 0x5A5A5A5A;
    uint32_t rdata0 = 0, rdata1 = 0;
    uint32_t exp_status = 0;
    uint32_t granularity = 64;

    const partition_t hw_part_uds = partitions[SECRET_MANUF_PARTITION];
    const partition_t hw_part_fe0 = partitions[SECRET_PROD_PARTITION_0];

    VPRINTF(LOW, "INFO: Starting shuffled UDS provisioning with 8 writes...\n");

    grant_caliptra_core_for_fc_writes();

    for (int i = 0; i < 8; i++) {
        uint8_t permutation_index = i % 5;
        VPRINTF(LOW, "INFO: Performing shuffled_dai_wr to UDS with permutation %d\n", permutation_index);
        shuffled_dai_wr(hw_part_uds.address+i*8, data0, data1, granularity, exp_status, permutation_index);
    }

    VPRINTF(LOW, "INFO: Revoking MCU access before triggering digest...\n");
    revoke_grant_mcu_for_fc_writes();

    VPRINTF(LOW, "INFO: Triggering calculate_digest_without_addr to test filter...\n");
    calculate_digest_without_addr(OTP_CTRL_STATUS_DAI_ERROR_MASK);

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    VPRINTF(LOW, "INFO: Granting MCU access again for FE0 provisioning...\n");
    grant_caliptra_core_for_fc_writes();

    VPRINTF(LOW, "INFO: Performing shuffled_dai_wr to FE0 with permutation 3\n");
    shuffled_dai_wr(hw_part_fe0.address, data0, data1, granularity, exp_status, 3);

    VPRINTF(LOW, "INFO: Revoking MCU access before triggering zeroize...\n");
    revoke_grant_mcu_for_fc_writes();

    VPRINTF(LOW, "INFO: Triggering zeroize_without_addr to test filter...\n");
    zeroize_without_addr(OTP_CTRL_STATUS_DAI_ERROR_MASK);

    VPRINTF(LOW, "INFO: Test sequence completed.\n");
}



void ocp_lock_zeroization(void) {
    uint32_t data[2];

    const partition_t hw_part = partitions[VENDOR_SECRET_PROD_PARTITION];
    const partition_t sw_part0 = partitions[CPTRA_SS_LOCK_HEK_PROD_0];
    const partition_t sw_part1 = partitions[CPTRA_SS_LOCK_HEK_PROD_1];

    // A partition that is not zeroizable.
    const partition_t ctrl_part = partitions[SW_MANUF_PARTITION];
    
    // The hardware partition gets locked for reads and writes after its
    // digest has been calculated via the DAI. Zeroization still needs
    // to work.

    // Write some data, read it back, and compare the data read back.
    uint32_t exp_data = 0xA5A5A5A5;
    data[0] = exp_data;
    data[1] = exp_data;
    dai_wr(hw_part.address, data[0], data[1], hw_part.granularity, 0);
    dai_rd(hw_part.address, &data[0], &data[1], hw_part.granularity, 0);
    if (data[0] != exp_data ||
            (hw_part.granularity > 32 && data[1] != exp_data)) {
        VPRINTF(LOW, "ERROR: read data does not match written data\n");
        goto epilogue;
    }

    // Lock the partition with a HW digest calculation.
    calculate_digest(hw_part.address, 0);

    // Reset to activate the write lock of the partition.
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // Zeroize fuse.
    if (!dai_zer(hw_part.address, hw_part.granularity, 0, false)) {
        VPRINTF(LOW, "ERROR: fuse is not zeroized\n");
        goto epilogue;
    }
    // Zeroize marker field.
    if (!dai_zer(hw_part.zer_address, 64, 0, false)) {
        VPRINTF(LOW, "ERROR: digest is not zeroized\n");
        goto epilogue;
    }

    // Zeroize the first 32-bit word of the software partition and its
    // digest. This partition is unbuffered, unlocked and
    // software-readable but the zeroization should nonetheless work.

    // Write some data, read it back, and compare the data read back
    exp_data = 0xA5A5A5A5;
    data[0] = exp_data;
    dai_wr(sw_part0.address, data[0], data[1], sw_part0.granularity, 0);
    dai_rd(sw_part0.address, &data[0], &data[1], sw_part0.granularity, 0);
    if (data[0] != exp_data) {
        VPRINTF(LOW, "ERROR: read data does not match written data\n");
        goto epilogue;
    }

    // This test does *not* lock the partition, to ensure that also
    // unlocked partitions can be zeroized.

    // Zeroize fuse. This test doesn't zeroize the marker field first,
    // to check that this also works. The next test will first zeroize
    // the marker field, which is the recommended flow.
    if (!dai_zer(sw_part0.address, sw_part0.granularity, 0, false)) {
        VPRINTF(LOW, "ERROR: fuse is not zeroized\n");
        goto epilogue;
    }
    // Zeroize marker field.
    if (!dai_zer(sw_part0.zer_address, 64, 0, false)) {
        VPRINTF(LOW, "ERROR: digest is not zeroized\n");
        goto epilogue;
    }

epilogue:
    VPRINTF(LOW, "ocp lock zeroization test finished\n");
}



void main(void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    VPRINTF(LOW, "INFO: Initializing Caliptra subsystem...\n");
    mcu_cptra_init_d();

    secret_with_shuffled_ops_with_fail();
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    ocp_lock_zeroization();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Final sleep loop
    }

    VPRINTF(LOW, "INFO: MCU Caliptra Boot sequence completed.\n");
    SEND_STDOUT_CTRL(0xff);
}
