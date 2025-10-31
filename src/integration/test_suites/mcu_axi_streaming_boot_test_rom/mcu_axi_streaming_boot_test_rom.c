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
//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
//
//
// Licensed under the Apache License, Version 2.0 (the \"License\");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an \"AS IS\" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//********************************************************************************"

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "string.h"
#include "stdint.h"
#include "veer-csr.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
// volatile char* stdout = (char *)0xd0580000;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif


void main (void) {

    int argc=0;
    char *argv[1];
    uint32_t i3c_reg_data;
    int err_count = 0;
    int loop_count = 0;

    // Initialize the printf library   
    VPRINTF(LOW, "=== MCU boot.. started == \n");

    //-- Boot MCU
    VPRINTF(LOW, "MCU: Booting...\n");
    boot_mcu();
    boot_i3c_core();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    //-- setting bypass mode for I3C
    i3c_reg_data = 0x00000000 | I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_CFG_REC_INTF_BYPASS_MASK; 
    lsu_write_32(SOC_I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_CFG, i3c_reg_data);
    VPRINTF(LOW,"I3C BYPASS mode set");

    VPRINTF(LOW, "=== MCU boot.. completed == \n");

    // Check if the I3C core is in the correct state
    i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_0);
    if (i3c_reg_data != 0x2050434f) {
        VPRINTF(LOW, "Error : I3C core not in the correct state\n");
        err_count++;
    }
    
    i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_1);
    if (i3c_reg_data != 0x56434552) {
        VPRINTF(LOW, "I3C core not in the correct state\n");
        err_count++;
    }

    // Read DEVICE_ID
    i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_0);
    if(i3c_reg_data != 1) {
        VPRINTF(FATAL, "DEVICE_ID_0 incorrect: expected: 0x%x actual: 0x%x\n", 1, i3c_reg_data);
    }

    // Read HW_STATUS
    i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS);
    if(i3c_reg_data != 0x00000100) {
        VPRINTF(FATAL, "HW_STATUS incorrect: expected: 0x%x actual: 0x%x\n", 0x100, i3c_reg_data);
    }

    // Read DEVICE_STATUS_0
    i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0);
    if(i3c_reg_data != 0) {
        VPRINTF(FATAL, "DEVICE_STATUS_0 incorrect: expected: 0x%x actual: 0x%x\n", 0x0, i3c_reg_data);
    }


    // waiting for recovery start
    while (1) {

        i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0);
        // i3c_reg_data == 0x00000003
        i3c_reg_data = i3c_reg_data & 0x00000003;
        VPRINTF(LOW, "I3C core device status is 0x%x\n", i3c_reg_data);
        if (i3c_reg_data == 0x00000003) {
            VPRINTF(LOW, "I3C core in recovery mode\n");
            break;
        }
        // Wait for the I3C core to finish the test
        VPRINTF(LOW, "Waiting for recovery start\n");
        mcu_sleep(1000);

    }

    //-- Read Recovery Status register for 0x00000001
    i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS);
    if (i3c_reg_data != 0x00000001) {
        VPRINTF(LOW, "I3C core recovery status is not set to 0x1\n");
        err_count++;
    }

    //-- writing RECOVERY_CTRL register
    i3c_reg_data = 0x00000000;
    lsu_write_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL, i3c_reg_data);
    VPRINTF(LOW, "I3C core recovery control register is set to 0x0\n");

    //-- writing INDIRECT_FIFO_CTRL Register 
    i3c_reg_data = 0x00000100;
    lsu_write_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_0, i3c_reg_data);
    VPRINTF(LOW, "I3C core indirect FIFO control register is set to 0x0100\n");

    //-- writing INDIRECT_FIFO_CTRL Register 1
    i3c_reg_data = 0x00000004;
    lsu_write_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_1, i3c_reg_data);
    VPRINTF(LOW, "I3C core indirect FIFO control register 1 is set to 0x00000001\n");

    //-- writing INDIRECT_FIFO_DATA Register
    i3c_reg_data = 0x12345678;
    lsu_write_32(SOC_I3CCSR_I3C_EC_TTI_TX_DATA_PORT, i3c_reg_data);
    VPRINTF(LOW, "I3C core indirect FIFO data register is set to 0x12345678\n");

    i3c_reg_data = 0xABCDCAFE;
    lsu_write_32(SOC_I3CCSR_I3C_EC_TTI_TX_DATA_PORT, i3c_reg_data);
    VPRINTF(LOW, "I3C core indirect FIFO data register is set to 0xABCDCAFE\n");

    i3c_reg_data = 0x23456789;
    lsu_write_32(SOC_I3CCSR_I3C_EC_TTI_TX_DATA_PORT, i3c_reg_data);
    VPRINTF(LOW, "I3C core indirect FIFO data register is set to 0x23456789\n");

    i3c_reg_data = 0xFEEDCAFE;
    lsu_write_32(SOC_I3CCSR_I3C_EC_TTI_TX_DATA_PORT, i3c_reg_data);
    VPRINTF(LOW, "I3C core indirect FIFO data register is set to 0xFEEDCAFE\n"); 

    //-- writing RECOVERY_CTRL Register
    i3c_reg_data = 0x00000F00;
    lsu_write_32(SOC_I3CCSR_I3C_EC_SOCMGMTIF_REC_INTF_REG_W1C_ACCESS, i3c_reg_data);
    VPRINTF(LOW, "I3C core recovery control register set to IMAGE ACTIVATION\n");

    // -- Read Recovery Status register to indicate RECOVERY SUCCESS by reading value 0x00000003
    while(1){
        
        loop_count = loop_count + 1;
        if(loop_count >= 100) {
          VPRINTF(LOW, "ERROR: Loop count beyond 100");
          err_count++;
          break;
        }

        i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS);
        if( i3c_reg_data != 0x00000002 || i3c_reg_data != 0x00000003 || i3c_reg_data != 0x00000004) { 
            VPRINTF(LOW, "I3C core recovery status is not set to expected value\n");
            err_count++;
        }
        if (i3c_reg_data == 0x00000003) {
            VPRINTF(LOW, "I3C core recovery status is set to 0x3\n");
            break;
        }
        // Wait for the I3C core to finish the test
        VPRINTF(LOW, "Waiting for recovery status update\n");
        mcu_sleep(1000);
    }

    if(err_count > 0) {
      VPRINTF(FATAL, "Test fails due to error");
    }


    //Halt the core to wait for Caliptra to finish the test
    csr_write_mpmc_halt();
}
