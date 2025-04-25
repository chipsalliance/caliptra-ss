
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
package tb_top_pkg;

    // -----------------------------------------------------------
    // Parameters
    // -----------------------------------------------------------
    // MCU SRAM
    localparam MCU_SRAM_SIZE_KB = 512;
    localparam MCU_SRAM_DATA_WIDTH   = 32;
    localparam MCU_SRAM_DATA_WIDTH_BYTES = MCU_SRAM_DATA_WIDTH / 8;
    localparam MCU_SRAM_ECC_WIDTH = 7;
    localparam MCU_SRAM_DATA_TOTAL_WIDTH = MCU_SRAM_DATA_WIDTH + MCU_SRAM_ECC_WIDTH;
    localparam MCU_SRAM_DEPTH   = (MCU_SRAM_SIZE_KB * 1024) / MCU_SRAM_DATA_WIDTH_BYTES;
    localparam MCU_SRAM_ADDR_WIDTH = $clog2(MCU_SRAM_DEPTH);

    // MCU Mailbox 0
    localparam MCU_MBOX0_SIZE_KB = 256;
    localparam MCU_MBOX0_DATA_W = 32;
    localparam MCU_MBOX0_ECC_DATA_W = 7;
    localparam MCU_MBOX0_SIZE_BYTES = MCU_MBOX0_SIZE_KB * 1024;
    localparam MCU_MBOX0_SIZE_DWORDS = MCU_MBOX0_SIZE_BYTES/4;
    localparam MCU_MBOX0_DATA_AND_ECC_W = MCU_MBOX0_DATA_W + MCU_MBOX0_ECC_DATA_W;
    localparam MCU_MBOX0_DEPTH = (MCU_MBOX0_SIZE_KB * 1024 * 8) / MCU_MBOX0_DATA_W;
    localparam MCU_MBOX0_ADDR_W = $clog2(MCU_MBOX0_DEPTH);
    localparam MCU_MBOX0_DEPTH_LOG2 = $clog2(MCU_MBOX0_DEPTH);
    localparam [4:0] SET_MCU_MBOX0_AXI_USER_INTEG   = { 1'b0,          1'b0,          1'b0,          1'b0,          1'b0};
    localparam [4:0][31:0] MCU_MBOX0_VALID_AXI_USER = {32'h4444_4444, 32'h3333_3333, 32'h2222_2222, 32'h1111_1111, 32'h0000_0000};

    // MCU Mailbox 1
    localparam MCU_MBOX1_SIZE_KB = 256;
    localparam MCU_MBOX1_DATA_W = 32;
    localparam MCU_MBOX1_ECC_DATA_W = 7;
    localparam MCU_MBOX1_SIZE_BYTES = MCU_MBOX1_SIZE_KB * 1024;
    localparam MCU_MBOX1_SIZE_DWORDS = MCU_MBOX1_SIZE_BYTES/4;
    localparam MCU_MBOX1_DATA_AND_ECC_W = MCU_MBOX1_DATA_W + MCU_MBOX1_ECC_DATA_W;
    localparam MCU_MBOX1_DEPTH = (MCU_MBOX1_SIZE_KB * 1024 * 8) / MCU_MBOX1_DATA_W;
    localparam MCU_MBOX1_ADDR_W = $clog2(MCU_MBOX1_DEPTH);
    localparam MCU_MBOX1_DEPTH_LOG2 = $clog2(MCU_MBOX1_DEPTH);
    localparam [4:0] SET_MCU_MBOX1_AXI_USER_INTEG   = { 1'b0,          1'b0,          1'b0,          1'b0,          1'b0};
    localparam [4:0][31:0] MCU_MBOX1_VALID_AXI_USER = {32'h4444_4444, 32'h3333_3333, 32'h2222_2222, 32'h1111_1111, 32'h0000_0000};

    `ifndef VERILATOR
      class bitflip_mask_generator #(
          int DATA_AND_ECC_W = 39
      );

        rand logic [DATA_AND_ECC_W-1:0] rand_sram_bitflip_mask;
        logic do_double_bitflip;
        constraint bitflip_c {
            if (do_double_bitflip) {
                $countones(rand_sram_bitflip_mask) == 2;
            } else {
                $countones(rand_sram_bitflip_mask) == 1;
            }
        }

        function new;
            this.rand_sram_bitflip_mask = '0;
            this.do_double_bitflip = 1'b0;
        endfunction

        function logic [DATA_AND_ECC_W-1:0] get_mask(bit do_double_bit = 1'b0);
            this.do_double_bitflip = do_double_bit;
            this.randomize();
            return this.rand_sram_bitflip_mask;
        endfunction

    endclass
    `else
    function static logic [39:0] get_bitflip_mask(bit do_double_bit = 1'b0);
        return 2 << ($urandom % (37)) | 39'(do_double_bit);
    endfunction
    `endif

    function static logic [39:0] get_bitflip_mask(bit do_double_bit = 1'b0);
        return 2 << ($urandom % (37)) | 39'(do_double_bit);
    endfunction 

    typedef struct packed {
        //  [1] - Double bit, DCCM Error Injection
        //  [0] - Single bit, DCCM Error Injection
        logic dccm_double_bit_error;
        logic dccm_single_bit_error;
    } veer_sram_error_injection_mode_t;

    typedef struct packed {
        //  [2] - Randomize when writes are injected
        //  [1] - Double bit, Mbox SRAM Error Injection
        //  [0] - Single bit, Mbox SRAM Error Injection
        logic randomize;
        logic double_bit_error;
        logic single_bit_error;
    } mcu_mbox_sram_error_injection_mode_t;

endpackage
