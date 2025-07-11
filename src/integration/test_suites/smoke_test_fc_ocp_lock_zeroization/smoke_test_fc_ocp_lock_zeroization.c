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
 * SW_MANUF_PARTITION and SECRET_LC_TRANSITION_PARTITION are zeroizable
 * while the others are not. This test verifies basic functionalities
 * of the zeroization flow.
 */
void ocp_lock_zeroization(void) {
    uint32_t data[2];

    const partition_t hw_part = partitions[SECRET_LC_TRANSITION_PARTITION];
    const partition_t sw_part = partitions[SW_MANUF_PARTITION];
    // A partition that is not zeroizable.
    const partition_t ctrl_part = partitions[VENDOR_SECRET_PROD_PARTITION];
    
    // Zeroize the first 64-bit word of the hardware SECRET_LC_TRANSITION_PARTITION
    // and its digest. This partition is buffered, secret and already locked.
    // Zeroization should work normally.

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

    // Zeroize the first 32-bit word of the software SW_MANUF_PARTITION
    // and its digest. This partition is unbuffered, unlocked and
    // software-readable but the zeroization should nonetheless work.

    // Zeroize fuse.
    dai_zer(sw_part.address, &data[0], &data[1], sw_part.granularity, 0);
    if (data[0] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: fuse is not zeroized\n");
        goto epilogue;
    }
    memset(data, 0, 2*sizeof(uint32_t));
    // Zeroize marker field.
    dai_zer(sw_part.zer_address, &data[0], &data[1], 64, 0);
    if (data[0] != 0xFFFFFFFF || data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: digest is not zeroized\n");
        goto epilogue;
    }
    memset(data, 0, 2*sizeof(uint32_t));

    // Attempting to zeroize a partition that is not zeroizable must
    // result in an error.
    dai_zer(ctrl_part.address, &data[0], &data[1], sw_part.granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK);
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
    dai_zer(sw_part.address, &data[0], &data[1], sw_part.granularity, 0);
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
    dai_rd(sw_part.zer_address, &data[0], &data[1], 64, 0);
    if (data[0] != 0xFFFFFFFF || data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: fuse is not zeroized\n");
        goto epilogue;
    }

epilogue:
    VPRINTF(LOW, "ocp lock zeroization test finished\n");
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    initialize_otp_controller();

    ocp_lock_zeroization();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
