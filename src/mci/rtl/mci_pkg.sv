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

    localparam MCU_MBOX_DATA_W = 32; //not configurable
    localparam MCU_MBOX_ECC_DATA_W = 7; //not configurable
    localparam MCU_DEF_MBOX_VALID_AXI_USER = 32'hFFFF_FFFF;

    // Assert reset for 10 cycles then deassert
    // to facilitate the hitless update
    parameter MCI_MCU_UPDATE_RESET_CYLES = 10;

    parameter  MCI_WDT_TIMEOUT_PERIOD_NUM_DWORDS = 2;
    localparam MCI_WDT_TIMEOUT_PERIOD_W = MCI_WDT_TIMEOUT_PERIOD_NUM_DWORDS * 32;

    //BOOT FSM
    // Encoding generated with
    // $ python3 sparse_fsm_encode.py -d 5 -m 13 -n 12 -s 14142135
    //
    // Minimum Hamming distance: 5
    // Maximum Hamming distance: 10
    //
    localparam int MCI_BOOT_FSM_STATE_WIDTH = 12;
    typedef enum logic [MCI_BOOT_FSM_STATE_WIDTH-1:0] {
        BOOT_IDLE               = 12'b100011001101,
        BOOT_OTP_FC             = 12'b110101101110,
        BOOT_LCC                = 12'b110110010110,
        BOOT_BREAKPOINT_CHECK   = 12'b101100011011,
        BOOT_BREAKPOINT         = 12'b100111110011,
        BOOT_MCU                = 12'b000110100101,
        BOOT_WAIT_CPTRA_GO      = 12'b011001101101,
        BOOT_CPTRA              = 12'b111011000011,
        BOOT_WAIT_MCU_RST_REQ   = 12'b111000110000,
        BOOT_HALT_MCU           = 12'b001111111100,
        BOOT_WAIT_MCU_HALTED    = 12'b100010101010,
        BOOT_RST_MCU            = 12'b010110001011,
        BOOT_ERROR              = 12'b001001010111
    } mci_boot_fsm_state_e;

    // Sequential, backwards-compatible 4-bit encoding of the sparse mci_boot_fsm_state_e
    // that is exposed to software via HW_FLOW_STATUS.boot_fsm. This is the single
    // source of truth shared by the RTL (mci_boot_seqr.boot_fsm_encoded) and the
    // verification environment, so the sparse encoding can change without touching either.
    // BOOT_ERROR and any invalid encoding report 4'hF.
    function automatic logic [3:0] mci_boot_fsm_state_encode(mci_boot_fsm_state_e state);
        unique case (state)
            BOOT_IDLE:             mci_boot_fsm_state_encode = 4'h0;
            BOOT_OTP_FC:           mci_boot_fsm_state_encode = 4'h1;
            BOOT_LCC:              mci_boot_fsm_state_encode = 4'h2;
            BOOT_BREAKPOINT_CHECK: mci_boot_fsm_state_encode = 4'h3;
            BOOT_BREAKPOINT:       mci_boot_fsm_state_encode = 4'h4;
            BOOT_MCU:              mci_boot_fsm_state_encode = 4'h5;
            BOOT_WAIT_CPTRA_GO:    mci_boot_fsm_state_encode = 4'h6;
            BOOT_CPTRA:            mci_boot_fsm_state_encode = 4'h7;
            BOOT_WAIT_MCU_RST_REQ: mci_boot_fsm_state_encode = 4'h8;
            BOOT_HALT_MCU:         mci_boot_fsm_state_encode = 4'h9;
            BOOT_WAIT_MCU_HALTED:  mci_boot_fsm_state_encode = 4'ha;
            BOOT_RST_MCU:          mci_boot_fsm_state_encode = 4'hb;
            BOOT_ERROR:            mci_boot_fsm_state_encode = 4'hf;
            default:               mci_boot_fsm_state_encode = 4'hf;
        endcase
    endfunction

    typedef enum logic [2:0] {
        TRANSLATOR_RESET            = 3'd0,
        TRANSLATOR_IDLE             = 3'd1,
        TRANSLATOR_NON_DEBUG        = 3'd2,
        TRANSLATOR_UNPROV_DEBUG     = 3'd3,
        TRANSLATOR_MANUF_NON_DEBUG  = 3'd4,
        TRANSLATOR_MANUF_DEBUG      = 3'd5,
        TRANSLATOR_PROD_NON_DEBUG   = 3'd6,
        TRANSLATOR_PROD_DEBUG       = 3'd7
    } mci_state_translator_fsm_state_e;

endpackage
`endif /*MCI_PKG*/
