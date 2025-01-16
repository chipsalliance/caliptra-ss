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

    typedef enum logic [3:0] {
        BOOT_IDLE               = 4'h0,
        BOOT_OTP_FC             = 4'h1,
        BOOT_LCC                = 4'h2,
        BOOT_BREAKPOINT         = 4'h3,
        BOOT_MCU                = 4'h4,
        BOOT_WAIT_CLPA_GO       = 4'h5,
        BOOT_CPTRA              = 4'h6,
        BOOT_WAIT_MCU_RST_REQ   = 4'h7,
        BOOT_RST_MCU            = 4'h8,
        BOOT_UNKNOWN             = 'x
    } mci_boot_fsm_state_e;

endpackage
`endif /*MCI_PKG*/
