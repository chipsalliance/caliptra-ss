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


void secret_prov(void) {
    VPRINTF(LOW, "INFO: Starting secret provisioning...\n");

    uint32_t data0 = 0xA5A5A5A5;
    uint32_t data1 = 0x5A5A5A5A;
    uint32_t rdata0 = 0xA5A5A5A5;
    uint32_t rdata1 = 0x5A5A5A5A;

    const partition_t hw_part_fe0 = partitions[SECRET_PROD_PARTITION_0];
    const partition_t hw_part_fe1 = partitions[SECRET_PROD_PARTITION_1];
    const partition_t hw_part_fe2 = partitions[SECRET_PROD_PARTITION_2];
    const partition_t hw_part_fe3 = partitions[SECRET_PROD_PARTITION_3];

    grant_caliptra_core_for_fc_writes();

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // Provision FE0
    VPRINTF(LOW, "INFO: Writing FE0 partition...\n");
    dai_wr(hw_part_fe0.address, data0, data1, hw_part_fe0.granularity, 0);

    VPRINTF(LOW, "INFO: FE0 partition should be readable...\n");
    dai_rd(hw_part_fe0.address, &rdata0, &rdata1, hw_part_fe0.granularity, 0);

    if (rdata0 != data0 || rdata1 != data1) {
        VPRINTF(LOW, "ERROR: FE0 fuse is not readble even though it is not locked!!!\n");
    }
    

    VPRINTF(LOW, "INFO: Calculating digest for FE0 partition...\n");
    calculate_digest(hw_part_fe0.address, 0);

    VPRINTF(LOW, "INFO: Resetting to activate FE0 partition lock...\n");
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    VPRINTF(LOW, "INFO: FE0 partition shouldn't be readable even by Caliptra...\n");
    dai_rd(hw_part_fe0.address, &rdata0, &rdata1, hw_part_fe0.granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK);

    if (rdata0 == data0 || rdata1 == data1) {
        VPRINTF(LOW, "ERROR: FE0 fuse is exposed!!!!\n");
    } else {
        VPRINTF(LOW, "PASS: FE0 fuse scrambled\n");
    }
    
    reset_fc_lcc_rtl();

    // Provision FE1
    VPRINTF(LOW, "INFO: Writing FE1 partition...\n");
    dai_wr(hw_part_fe1.address, data0, data1, hw_part_fe1.granularity, 0);

    revoke_grant_mcu_for_fc_writes();

    VPRINTF(LOW, "INFO: FE1 partition should't be readable by MCU...\n");
    VPRINTF(LOW, "DEBUG: Triggering DAI read command.\n");
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_CMD, 0x1);

    wait_dai_op_idle(OTP_CTRL_STATUS_DAI_ERROR_MASK);

    rdata0 = lsu_read_32(SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_0);
    VPRINTF(LOW, "DEBUG: Read data from DIRECT_ACCESS_RDATA_0: 0x%08X\n", rdata0);

    if (hw_part_fe1.granularity == 64) {
        rdata1 = lsu_read_32(SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_1);
        VPRINTF(LOW, "DEBUG: Read data from DIRECT_ACCESS_RDATA_1: 0x%08X\n", rdata1);
    }

    reset_fc_lcc_rtl();
    grant_caliptra_core_for_fc_writes();

    VPRINTF(LOW, "INFO: Calculating digest for FE1 partition...\n");
    calculate_digest(hw_part_fe1.address, 0);

    VPRINTF(LOW, "INFO: Resetting to activate FE1 partition lock...\n");
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    VPRINTF(LOW, "INFO: FE1 partition shouldn't be readable even by Caliptra...\n");
    dai_rd(hw_part_fe1.address, &rdata0, &rdata1, hw_part_fe1.granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK);

    if (rdata0 == data0 || rdata1 == data1) {
        VPRINTF(LOW, "ERROR: FE1 fuse is exposed!!!!\n");
    } else {
        VPRINTF(LOW, "PASS: FE1 fuse scrambled\n");
    }

    reset_fc_lcc_rtl();
    // Provision FE2
    VPRINTF(LOW, "INFO: Writing FE2 partition...\n");
    dai_wr(hw_part_fe2.address, data0, data1, hw_part_fe2.granularity, 0);

    revoke_grant_mcu_for_fc_writes();
    VPRINTF(LOW, "DEBUG: Address sent by MCU but CMD sent by Caliptra\n");
    VPRINTF(LOW, "DEBUG: Writing address: 0x%08X to DIRECT_ACCESS_ADDRESS.\n", hw_part_fe2.address);
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS, hw_part_fe2.address);

    grant_caliptra_core_for_fc_writes();

    VPRINTF(LOW, "INFO: FE2 partition should't be readable by MCU...\n");
    VPRINTF(LOW, "DEBUG: Triggering DAI read command.\n");
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_CMD, 0x1);

    wait_dai_op_idle(OTP_CTRL_STATUS_DAI_ERROR_MASK);

    rdata0 = lsu_read_32(SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_0);
    VPRINTF(LOW, "DEBUG: Read data from DIRECT_ACCESS_RDATA_0: 0x%08X\n", rdata0);

    if (hw_part_fe2.granularity == 64) {
        rdata1 = lsu_read_32(SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_1);
        VPRINTF(LOW, "DEBUG: Read data from DIRECT_ACCESS_RDATA_1: 0x%08X\n", rdata1);
    }

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);
    VPRINTF(LOW, "INFO: Calculating digest for FE2 partition...\n");
    calculate_digest(hw_part_fe2.address, 0);

    VPRINTF(LOW, "INFO: Resetting to activate FE2 partition lock...\n");
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    VPRINTF(LOW, "INFO: FE2 partition shouldn't be readable even by Caliptra...\n");
    dai_rd(hw_part_fe2.address, &rdata0, &rdata1, hw_part_fe2.granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK);

    if (rdata0 == data0 || rdata1 == data1) {
        VPRINTF(LOW, "ERROR: FE2 fuse is exposed!!!!\n");
    } else {
        VPRINTF(LOW, "PASS: FE2 fuse scrambled\n");
    }




    VPRINTF(LOW, "INFO: Secret provisioning completed.\n");
}

void main(void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    VPRINTF(LOW, "INFO: Initializing Caliptra subsystem...\n");
    mcu_cptra_init_d();

    secret_prov();

    VPRINTF(LOW, "INFO: MCU Caliptra Boot sequence completed.\n");
    SEND_STDOUT_CTRL(0xff);
}
