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
//

module caliptra_ss_veer_sram_export import css_mcu0_el2_pkg::*; #(
    `include "css_mcu0_el2_param.vh"
) (
    css_mcu0_el2_mem_if cptra_ss_mcu0_el2_mem_export
);

    logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_fdata_bank;
    logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-1:0] dccm_bank_fdout;

//////////////////////////////////////////////////////
// DCCM
//
if (pt.DCCM_ENABLE == 1) begin: css_mcu0_dccm_enable
    `define MCU_LOCAL_DCCM_RAM_TEST_PORTS   .TEST1   (1'b0   ), \
                                            .RME     (1'b0   ), \
                                            .RM      (4'b0000), \
                                            .LS      (1'b0   ), \
                                            .DS      (1'b0   ), \
                                            .SD      (1'b0   ), \
                                            .TEST_RNM(1'b0   ), \
                                            .BC1     (1'b0   ), \
                                            .BC2     (1'b0   ), \

    logic [pt.DCCM_NUM_BANKS-1:0] [pt.DCCM_FDATA_WIDTH-1:0] dccm_wdata_bitflip;
    int ii;
    localparam DCCM_INDEX_DEPTH = ((pt.DCCM_SIZE)*1024)/((pt.DCCM_BYTE_WIDTH)*(pt.DCCM_NUM_BANKS));  // Depth of memory bank
    // 8 Banks, 16KB each (2048 x 72)
    always_ff @(cptra_ss_mcu0_el2_mem_export.clk) begin : inject_dccm_ecc_error
        // if (~error_injection_mode.dccm_single_bit_error && ~error_injection_mode.dccm_double_bit_error) begin
        //     dccm_wdata_bitflip <= '{default:0};
        // end else if (cptra_ss_mcu0_el2_mem_export.dccm_clken & cptra_ss_mcu0_el2_mem_export.dccm_wren_bank) begin
        //     for (ii=0; ii<pt.DCCM_NUM_BANKS; ii++) begin: dccm_bitflip_injection_loop
        //         dccm_wdata_bitflip[ii] <= get_bitflip_mask(error_injection_mode.dccm_double_bit_error);
        //     end
        // end
        dccm_wdata_bitflip <= '{default:0};
    end
    for (genvar i=0; i<pt.DCCM_NUM_BANKS; i++) begin: dccm_loop

        assign dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0] = {cptra_ss_mcu0_el2_mem_export.dccm_wr_ecc_bank[i], cptra_ss_mcu0_el2_mem_export.dccm_wr_data_bank[i]} ^ dccm_wdata_bitflip[i];
        assign cptra_ss_mcu0_el2_mem_export.dccm_bank_dout[i] = dccm_bank_fdout[i][31:0];
        assign cptra_ss_mcu0_el2_mem_export.dccm_bank_ecc[i] = dccm_bank_fdout[i][38:32];

    `ifdef VERILATOR

            el2_ram #(DCCM_INDEX_DEPTH,39)  ram (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
    `else

        if (DCCM_INDEX_DEPTH == 32768) begin : dccm
	 	 	 	 css_mcu0_ram_32768x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 16384) begin : dccm
	 	 	 	 css_mcu0_ram_16384x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 8192) begin : dccm
	 	 	 	 css_mcu0_ram_8192x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 4096) begin : dccm
	 	 	 	 css_mcu0_ram_4096x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 3072) begin : dccm
	 	 	 	 css_mcu0_ram_3072x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 2048) begin : dccm
	 	 	 	 css_mcu0_ram_2048x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 1024) begin : dccm
	 	 	 	 css_mcu0_ram_1024x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 512) begin : dccm
	 	 	 	 css_mcu0_ram_512x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 256) begin : dccm
	 	 	 	 css_mcu0_ram_256x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 128) begin : dccm
	 	 	 	 css_mcu0_ram_128x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
    `endif
    end : dccm_loop
end :css_mcu0_dccm_enable

`include "icache_macros.svh"

// ICACHE tie offs
 if (pt.ICACHE_WAYPACK == 0 ) begin : VEER_TIE_OFF_PACKED
     `EL2_TIE_OFF_PACKED(cptra_ss_mcu0_el2_mem_export)
 end // VEER_TIE_OFF_UNPACKED
 else begin: VEER_TIE_OFF_UNPACKED
     `EL2_TIE_OFF_NON_PACKED(cptra_ss_mcu0_el2_mem_export)
 end // VEER_TIE_OFF_PACKED

// ICACHE DATA
 if (pt.ICACHE_WAYPACK == 0 ) begin : PACKED_0
    for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin: WAYS
      for (genvar k=0; k<pt.ICACHE_BANKS_WAY; k++) begin: BANKS_WAY   // 16B subbank
      if (pt.ICACHE_ECC) begin : ECC1
        if ($clog2(pt.ICACHE_DATA_DEPTH) == 13 )   begin : size_8192
           `EL2_IC_DATA_SRAM(8192,71,i,k,cptra_ss_mcu0_el2_mem_export)
        end
        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
           `EL2_IC_DATA_SRAM(4096,71,i,k,cptra_ss_mcu0_el2_mem_export)
        end
        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
           `EL2_IC_DATA_SRAM(2048,71,i,k,cptra_ss_mcu0_el2_mem_export)
        end
        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
           `EL2_IC_DATA_SRAM(1024,71,i,k,cptra_ss_mcu0_el2_mem_export)
        end
        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
           `EL2_IC_DATA_SRAM(512,71,i,k,cptra_ss_mcu0_el2_mem_export)
        end
         else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
           `EL2_IC_DATA_SRAM(256,71,i,k,cptra_ss_mcu0_el2_mem_export)
         end
         else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
           `EL2_IC_DATA_SRAM(128,71,i,k,cptra_ss_mcu0_el2_mem_export)
         end
         else  begin : size_64
           `EL2_IC_DATA_SRAM(64,71,i,k,cptra_ss_mcu0_el2_mem_export)
         end
      end // if (pt.ICACHE_ECC)

     else  begin  : ECC0
        if ($clog2(pt.ICACHE_DATA_DEPTH) == 13 )   begin : size_8192
           `EL2_IC_DATA_SRAM(8192,68,i,k,cptra_ss_mcu0_el2_mem_export)
        end
        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
           `EL2_IC_DATA_SRAM(4096,68,i,k,cptra_ss_mcu0_el2_mem_export)
        end
        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
           `EL2_IC_DATA_SRAM(2048,68,i,k,cptra_ss_mcu0_el2_mem_export)
        end
        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
           `EL2_IC_DATA_SRAM(1024,68,i,k,cptra_ss_mcu0_el2_mem_export)
        end
        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
           `EL2_IC_DATA_SRAM(512,68,i,k,cptra_ss_mcu0_el2_mem_export)
        end
         else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
           `EL2_IC_DATA_SRAM(256,68,i,k,cptra_ss_mcu0_el2_mem_export)
         end
         else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
           `EL2_IC_DATA_SRAM(128,68,i,k,cptra_ss_mcu0_el2_mem_export)
         end
         else  begin : size_64
           `EL2_IC_DATA_SRAM(64,68,i,k,cptra_ss_mcu0_el2_mem_export)
         end
      end // else: !if(pt.ICACHE_ECC)
      end // block: BANKS_WAY
   end // block: WAYS

 end // block: PACKED_0

 // WAY PACKED
 else begin : PACKED_10

 // generate IC DATA PACKED SRAMS for 2/4 ways
  for (genvar k=0; k<pt.ICACHE_BANKS_WAY; k++) begin: BANKS_WAY   // 16B subbank
     if (pt.ICACHE_ECC) begin : ECC1
        // SRAMS with ECC (single/double detect; no correct)
        if ($clog2(pt.ICACHE_DATA_DEPTH) == 13 )   begin : size_8192
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(8192,284,71,k,cptra_ss_mcu0_el2_mem_export)    // 64b data + 7b ecc
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(8192,142,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_8192

        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(4096,284,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(4096,142,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_4096

        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(2048,284,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(2048,142,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_2048

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(1024,284,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(1024,142,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_1024

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(512,284,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(512,142,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_512

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(256,284,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(256,142,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_256

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(128,284,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(128,142,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_128

        else  begin : size_64
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(64,284,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(64,142,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_64
       end // if (pt.ICACHE_ECC)

     else  begin  : ECC0
        // SRAMs with parity
        if ($clog2(pt.ICACHE_DATA_DEPTH) == 13 )   begin : size_8192
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(8192,272,68,k,cptra_ss_mcu0_el2_mem_export)    // 64b data + 4b parity
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(8192,136,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_8192

        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(4096,272,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(4096,136,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_4096

        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(2048,272,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(2048,136,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_2048

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(1024,272,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(1024,136,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_1024

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(512,272,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(512,136,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_512

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(256,272,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(256,136,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_256

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(128,272,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(128,136,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_128

        else  begin : size_64
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(64,272,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(64,136,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_64
     end // block: ECC0
     end // block: BANKS_WAY
 end // block: PACKED_10


// ICACHE TAG
if (pt.ICACHE_WAYPACK == 0 ) begin : PACKED_11
    for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin: WAYS
        if (pt.ICACHE_TAG_DEPTH == 32)   begin : size_32
                 `EL2_IC_TAG_SRAM(32,26,i,cptra_ss_mcu0_el2_mem_export)
        end // if (pt.ICACHE_TAG_DEPTH == 32)
        if (pt.ICACHE_TAG_DEPTH == 64)   begin : size_64
                 `EL2_IC_TAG_SRAM(64,26,i,cptra_ss_mcu0_el2_mem_export)
        end // if (pt.ICACHE_TAG_DEPTH == 64)
        if (pt.ICACHE_TAG_DEPTH == 128)   begin : size_128
                 `EL2_IC_TAG_SRAM(128,26,i,cptra_ss_mcu0_el2_mem_export)
        end // if (pt.ICACHE_TAG_DEPTH == 128)
        if (pt.ICACHE_TAG_DEPTH == 256)   begin : size_256
                 `EL2_IC_TAG_SRAM(256,26,i,cptra_ss_mcu0_el2_mem_export)
        end // if (pt.ICACHE_TAG_DEPTH == 256)
        if (pt.ICACHE_TAG_DEPTH == 512)   begin : size_512
                 `EL2_IC_TAG_SRAM(512,26,i,cptra_ss_mcu0_el2_mem_export)
        end // if (pt.ICACHE_TAG_DEPTH == 512)
        if (pt.ICACHE_TAG_DEPTH == 1024)   begin : size_1024
                 `EL2_IC_TAG_SRAM(1024,26,i,cptra_ss_mcu0_el2_mem_export)
        end // if (pt.ICACHE_TAG_DEPTH == 1024)
        if (pt.ICACHE_TAG_DEPTH == 2048)   begin : size_2048
                 `EL2_IC_TAG_SRAM(2048,26,i,cptra_ss_mcu0_el2_mem_export)
        end // if (pt.ICACHE_TAG_DEPTH == 2048)
        if (pt.ICACHE_TAG_DEPTH == 4096)   begin  : size_4096
                 `EL2_IC_TAG_SRAM(4096,26,i,cptra_ss_mcu0_el2_mem_export)
        end // if (pt.ICACHE_TAG_DEPTH == 4096)
   end // block: WAYS
 end // block: PACKED_11

 else begin : PACKED_1
    if (pt.ICACHE_ECC) begin  : ECC1
      if (pt.ICACHE_TAG_DEPTH == 32)   begin : size_32
        if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(32,104,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(32,52,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // if (pt.ICACHE_TAG_DEPTH == 32

      if (pt.ICACHE_TAG_DEPTH == 64)   begin : size_64
        if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(64,104,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(64,52,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_64

      if (pt.ICACHE_TAG_DEPTH == 128)   begin : size_128
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(128,104,cptra_ss_mcu0_el2_mem_export)
      end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(128,52,cptra_ss_mcu0_el2_mem_export)
      end // block: WAYS

      end // block: size_128

      if (pt.ICACHE_TAG_DEPTH == 256)   begin : size_256
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(256,104,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(256,52,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_256

      if (pt.ICACHE_TAG_DEPTH == 512)   begin : size_512
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(512,104,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(512,52,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_512

      if (pt.ICACHE_TAG_DEPTH == 1024)   begin : size_1024
         if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(1024,104,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(1024,52,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_1024

      if (pt.ICACHE_TAG_DEPTH == 2048)   begin : size_2048
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(2048,104,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(2048,52,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_2048

      if (pt.ICACHE_TAG_DEPTH == 4096)   begin  : size_4096
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(4096,104,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(4096,52,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_4096
   end // block: ECC1

   else  begin : ECC0
      if (pt.ICACHE_TAG_DEPTH == 32)   begin : size_32
        if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(32,88,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(32,44,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // if (pt.ICACHE_TAG_DEPTH == 32

      if (pt.ICACHE_TAG_DEPTH == 64)   begin : size_64
        if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(64,88,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(64,44,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_64

      if (pt.ICACHE_TAG_DEPTH == 128)   begin : size_128
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(128,88,cptra_ss_mcu0_el2_mem_export)
      end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(128,44,cptra_ss_mcu0_el2_mem_export)
      end // block: WAYS

      end // block: size_128

      if (pt.ICACHE_TAG_DEPTH == 256)   begin : size_256
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(256,88,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(256,44,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_256

      if (pt.ICACHE_TAG_DEPTH == 512)   begin : size_512
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(512,88,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(512,44,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_512

      if (pt.ICACHE_TAG_DEPTH == 1024)   begin : size_1024
         if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(1024,88,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(1024,44,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_1024

      if (pt.ICACHE_TAG_DEPTH == 2048)   begin : size_2048
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(2048,88,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(2048,44,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_2048

      if (pt.ICACHE_TAG_DEPTH == 4096)   begin  : size_4096
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(4096,88,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(4096,44,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_4096
   end // block: ECC0
end // block: PACKED_1
// end ICACHE TAG

endmodule
