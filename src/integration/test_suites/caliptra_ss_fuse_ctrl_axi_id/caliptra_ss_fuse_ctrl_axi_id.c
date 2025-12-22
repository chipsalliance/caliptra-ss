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
 * This test performs DAI writes over the AXI bus on the boundaries of the
 * fuse controller access table entries with randomized fuse writes and
 * random AXI user ids.
 */


 const uint32_t tokens[13][4] = {
    [RAU] = {CPTRA_SS_LC_CTRL_RAW_UNLOCK_TOKEN},              // RAW_UNLOCK
    [TU1] = {0x72f04808, 0x05f493b4, 0x7790628a, 0x318372c8}, // TEST_UNLOCKED1
    [TU2] = {0x17c78a78, 0xc7b443ef, 0xd6931045, 0x55e74f3c}, // TEST_UNLOCKED2
    [TU3] = {0x1644aa12, 0x79925802, 0xdbc26815, 0x8597a5fa}, // TEST_UNLOCKED3
    [TU4] = {0x34d1ea6e, 0x121f023f, 0x6e9dc51c, 0xc7439b6f}, // TEST_UNLOCKED4
    [TU5] = {0x03fd9df1, 0x20978af4, 0x49db216d, 0xb0225ece}, // TEST_UNLOCKED5
    [TU6] = {0xcfc0871c, 0xc400e922, 0x4290a4ad, 0x7f10dc89}, // TEST_UNLOCKED6
    [TU7] = {0x67e87f3e, 0xae6ee167, 0x802efa05, 0xbaaa3138}, // TEST_UNLOCKED7
    [TEX] = {0x2f533ae9, 0x341d2478, 0x5f066362, 0xb5fe1577}, // TEST_EXIT
    [DEX] = {0xf622abb6, 0x5d8318f4, 0xc721179d, 0x51c001f2}, // DEV_EXIT
    [PEX] = {0x25b8649d, 0xe7818e5b, 0x826d5ba4, 0xd6b633a0}, // PROD_EXIT
    [RMU] = {0x72f04808, 0x05f493b4, 0x7790628a, 0x318372c8}, // RMA
    [ZER] = {0}                                               // ZERO
};



// Write data to the first entry of the given partition, then
// calculate a digest for the partition. Return true if every step
// succeeds.
bool provision_partition(const char *name,
                         const partition_t *part,
                         const uint32_t data[2], uint32_t expected_outcome) {
    VPRINTF(LOW, "INFO: Writing %s partition...\n", name);
    if (!dai_wr(part->address, data[0], data[1], part->granularity, expected_outcome))
        return false;
    if (expected_outcome != 0) {
        return true; // No need to calculate digest if write failed as expected
    }
    VPRINTF(LOW, "INFO: Calculating digest for %s partition...\n", name);
    return calculate_digest(part->address, expected_outcome);
}

// Write data to provision each secret partition. Return true if this
// succeeds.
bool secret_prov(uint32_t choose_partition, uint32_t expected_outcome) {
    VPRINTF(LOW, "INFO: Starting secret provisioning...\n");

    uint32_t data[2] = { 0xA5A5A5A5, 0x5A5A5A5A };

    if (choose_partition == 0) {
        if (!provision_partition("UDS", &partitions[SECRET_MANUF_PARTITION], data, expected_outcome))
            return false;
    }
    else if (choose_partition == 1) {
        if (!provision_partition("FE0", &partitions[SECRET_PROD_PARTITION_0], data, expected_outcome))
            return false;
    }
    else if (choose_partition == 2) {
        if (!provision_partition("FE1", &partitions[SECRET_PROD_PARTITION_1], data, expected_outcome))
            return false;
    }
    else if (choose_partition == 3) {
        if (!provision_partition("FE2", &partitions[SECRET_PROD_PARTITION_2], data, expected_outcome))
            return false;
    }   
    else if (choose_partition == 4) {
         if (!provision_partition("FE3", &partitions[SECRET_PROD_PARTITION_3], data, expected_outcome))
            return false;
    }
    else if (choose_partition == 5) {
         if (!provision_partition("VENDOR_SECRET", &partitions[VENDOR_SECRET_PROD_PARTITION], data, expected_outcome))
            return false;
    }
    else {    
        handle_error("ERROR: Invalid partition choice %d for secret provisioning.\n", choose_partition);
        return false;
    }

    VPRINTF(LOW, "INFO: Secret provisioning completed.\n");
    return true;
}


bool body(void) {
    VPRINTF(LOW, "\n\n------------------------------\n\n");
    VPRINTF(LOW, "INFO: Initializing Caliptra subsystem...\n");
    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    uint32_t expected_outcome = 0;

    bool axi_user = xorshift32() % 2; // 0 is makes MCU Caliptra core, 1 keeps MCU idendtity

    if (!axi_user){
        VPRINTF(LOW, "INFO: Granting MCU access to fuse controller...\n");
        grant_caliptra_core_for_fc_writes();
    }

    uint32_t choose_partition = xorshift32() % 6; // 0-5 for 6 partitions

    if (axi_user && choose_partition != 5){
        expected_outcome = OTP_CTRL_STATUS_DAI_ERROR_MASK;
    }

  

    VPRINTF(LOW, "INFO: Starting secret provisioning sequence...\n");
    if ( secret_prov(choose_partition, expected_outcome)){
        VPRINTF(LOW, "INFO: Secret provisioning sequence completed as expected.\n");
    }
    else{
        handle_error("ERROR: Secret provisioning sequence failed...\n");
        return false;
    }
    VPRINTF(LOW, "\n\n------------------------------\n\n");

    return true;
}




void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");
    
    if (!body())
        handle_error("FC AXI ID check failed.\n");
    else
        VPRINTF(LOW, "FC AXI ID check passed.\n");


    SEND_STDOUT_CTRL(0xff);
}
