// SPDX-License-Identifier: Apache-2.0
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

`ifndef MCI_PKG
    `define MCI_PKG

package mci_pkg;
    localparam KB = 1024;
    localparam KB_BASE0 = KB - 1;
    localparam MB = KB * 1024;
    localparam MB_BASE0 = MB - 1;

    // Assert reset for 10 cycles then deassert
    // to facilitate the hitless update
    parameter MCI_MCU_UPDATE_RESET_CYLES = 10;

    parameter  MCI_WDT_TIMEOUT_PERIOD_NUM_DWORDS = 2;
    localparam MCI_WDT_TIMEOUT_PERIOD_W = MCI_WDT_TIMEOUT_PERIOD_NUM_DWORDS * 32;

    //Mailbox size configuration
    parameter MCI_MBOX0_SIZE_KB = 4;
    parameter MCI_MBOX0_DATA_W = 32;
    parameter MCI_MBOX0_ECC_DATA_W = 7;
    parameter MCI_MBOX0_SIZE_BYTES = MCI_MBOX0_SIZE_KB * 1024;
    parameter MCI_MBOX0_SIZE_DWORDS = MCI_MBOX0_SIZE_BYTES/4;
    parameter MCI_MBOX0_DATA_AND_ECC_W = MCI_MBOX0_DATA_W + MCI_MBOX0_ECC_DATA_W;
    parameter MCI_MBOX0_DEPTH = (MCI_MBOX0_SIZE_KB * 1024 * 8) / MCI_MBOX0_DATA_W;
    parameter MCI_MBOX0_ADDR_W = $clog2(MCI_MBOX0_DEPTH);
    parameter MCI_MBOX0_DEPTH_LOG2 = $clog2(MCI_MBOX0_DEPTH);

    parameter MCI_MBOX1_SIZE_KB = 4;
    parameter MCI_MBOX1_DATA_W = 32;
    parameter MCI_MBOX1_ECC_DATA_W = 7;
    parameter MCI_MBOX1_SIZE_BYTES = MCI_MBOX1_SIZE_KB * 1024;
    parameter MCI_MBOX1_SIZE_DWORDS = MCI_MBOX1_SIZE_BYTES/4;
    parameter MCI_MBOX1_DATA_AND_ECC_W = MCI_MBOX1_DATA_W + MCI_MBOX1_ECC_DATA_W;
    parameter MCI_MBOX1_DEPTH = (MCI_MBOX1_SIZE_KB * 1024 * 8) / MCI_MBOX1_DATA_W;
    parameter MCI_MBOX1_ADDR_W = $clog2(MCI_MBOX1_DEPTH);
    parameter MCI_MBOX1_DEPTH_LOG2 = $clog2(MCI_MBOX1_DEPTH);

    typedef enum logic [3:0] {
        BOOT_IDLE          = 4'b0000,
        BOOT_FABRIC        = 4'b0001,
        BOOT_OTP_FC        = 4'b0010,
        BOOT_LCC           = 4'b0011,
        BOOT_MCU           = 4'b0100,
        BOOT_PLL           = 4'b0101,
        BOOT_WAIT_MCI    = 4'b0110,
        BOOT_MCI         = 4'b0111,
        BOOT_WAIT_UPDATE   = 4'b1000,
        BOOT_RST_MCU       = 4'b1001
    } mci_boot_fsm_state_e;

endpackage
`endif /*MCI_PKG*/
