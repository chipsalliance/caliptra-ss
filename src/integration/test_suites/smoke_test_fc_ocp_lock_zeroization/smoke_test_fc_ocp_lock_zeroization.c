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

/**
 * VENDOR_SECRET_PROD_PARTITION and CPTRA_SS_LOCK_HEK_PROD_* partitions
 * are zeroizable while the others are not. This test verifies basic
 * functionalities of the zeroization flow.
 */
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
    dai_wr(hw_part.address, data[0], data[1], hw_part.granularity, 0);
    dai_rd(hw_part.address, &data[0], &data[1], hw_part.granularity, 0);
    if (data[0] != exp_data) {
        VPRINTF(LOW, "ERROR: read data does not match written data\n");
        goto epilogue;
    }

    // Lock the partition with a HW digest calculation.
    calculate_digest(hw_part.address, 0);

    // Zeroize fuse.
    dai_zer(hw_part.address, &data[0], &data[1], hw_part.granularity, 0);
    if (data[0] != 0xFFFFFFFF || data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: fuse is not zeroized\n");
        goto epilogue;
    }
    memset(data, 0, 2*sizeof(uint32_t));
    // Zeroize marker field.
    dai_zer(hw_part.zer_address, &data[0], &data[1], 64, 0);
    if (data[0] != 0xFFFFFFFF || data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: digest is not zeroized\n");
        goto epilogue;
    }
    memset(data, 0, 2*sizeof(uint32_t));

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
    dai_zer(sw_part0.address, &data[0], &data[1], sw_part0.granularity, 0);
    if (data[0] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: fuse is not zeroized\n");
        goto epilogue;
    }
    memset(data, 0, 2*sizeof(uint32_t));
    // Zeroize marker field.
    dai_zer(sw_part0.zer_address, &data[0], &data[1], 64, 0);
    if (data[0] != 0xFFFFFFFF || data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: digest is not zeroized\n");
        goto epilogue;
    }
    memset(data, 0, 2*sizeof(uint32_t));

    // Write, then calculate & write digest, then read an unbuffered
    // partition. Finally, zeroize the partition.
    exp_data = 0xA5A5A5A5;
    data[0] = exp_data;
    dai_wr(sw_part1.address, data[0], data[1], sw_part1.granularity, 0);
    // This is a software partition that needs to be locked manually by firmware.
    dai_wr(sw_part1.digest_address, 0x12, 0x34, 64, 0);
    dai_rd(sw_part1.address, &data[0], &data[1], sw_part1.granularity, 0);
    if (data[0] != exp_data) {
        VPRINTF(LOW, "ERROR: read data does not match written data\n");
        goto epilogue;
    }
    // Zeroize marker before data, as recommended.
    dai_zer(sw_part1.zer_address, &data[0], &data[1], 64, 0);
    if (data[0] != 0xFFFFFFFF || data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: marker is not zeroized\n");
        goto epilogue;
    }
    memset(data, 0, 2*sizeof(uint32_t));
    dai_zer(sw_part1.address, &data[0], &data[1], sw_part1.granularity, 0);
    if (data[0] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: data is not zeroized\n");
        goto epilogue;
    }
    memset(data, 0, 2*sizeof(uint32_t));

    // Attempting to zeroize a partition that is not zeroizable must
    // result in an error.
    dai_zer(ctrl_part.address, &data[0], &data[1], sw_part0.granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    if (data[0] != 0x0 || data[1] != 0x0) {
        VPRINTF(LOW, "ERROR: fuse is not 0.\n");
        goto epilogue;
    }

    // A reset triggers a integrity check that must skip the zeroized
    // partitions.

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // Zeroization is idempotent, meaning that repeated zeroizations
    // have the same effect.

    // Hw part fuse.
    dai_zer(hw_part.address, &data[0], &data[1], hw_part.granularity, 0);
    if (data[0] != 0xFFFFFFFF || data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: fuse is not zeroized\n");
        goto epilogue;
    }
    memset(data, 0, 2*sizeof(uint32_t));
    // Sw part fuse.
    dai_zer(sw_part0.address, &data[0], &data[1], sw_part0.granularity, 0);
    if (data[0] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: fuse is not zeroized\n");
        goto epilogue;
    }
    memset(data, 0, 2*sizeof(uint32_t));

    // Reading the zeroization field should still work, now without ECC.
    dai_rd(hw_part.zer_address, &data[0], &data[1], hw_part.granularity, 0);
    if (data[0] != 0xFFFFFFFF || data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: fuse is not zeroized\n");
        goto epilogue;
    }
    memset(data, 0, 2*sizeof(uint32_t));
    dai_rd(sw_part0.zer_address, &data[0], &data[1], 64, 0);
    if (data[0] != 0xFFFFFFFF || data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: fuse is not zeroized\n");
        goto epilogue;
    }

    // Lock the first three ratchet seed partition
    lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 0x3);

    // Check that for a locked partition, neither the data nor the
    // digest can be written.
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_2].address, 0xFF, 0xFF, 32, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_2].digest_address, 0x12, 0x34, 64, 0);

    // Check that a non-locked partition can still be written.
    dai_wr(partitions[CPTRA_SS_LOCK_HEK_PROD_3].address, 0xFF, 0xFF, 32, 0);

epilogue:
    VPRINTF(LOW, "ocp lock zeroization test finished\n");
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    ocp_lock_zeroization();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
