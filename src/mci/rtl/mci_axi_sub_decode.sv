
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
// Description:
//      Decodes the SOC request and sends to appropriate target.
//
`include "caliptra_prim_assert.sv"
`include "caliptra_sva.svh"

module mci_axi_sub_decode 
    import mci_pkg::*;
    import mci_reg_pkg::*;
    import mcu_mbox_csr_pkg::*;
    import trace_buffer_csr_pkg::*;
    #(
    // Configurable memory blocks
    parameter MCU_SRAM_SIZE_KB = 512,

    ///////////////////////////////////////////////////////////
    // MCI Memory Map
    ///////////////////////////////////////////////////////////
    // NOTE: Update parameters if adding/removing IPs to the address space.
    localparam MCI_REG_SIZE_BYTES               = 2 ** MCI_REG_MIN_ADDR_WIDTH, 
    localparam MCI_REG_START_ADDR               = 32'h0000_0000,
    localparam MCI_REG_END_ADDR                 = MCI_REG_START_ADDR + (MCI_REG_SIZE_BYTES) - 1,
    localparam MCU_TRACE_BUFFER_SIZE_BYTES      = 2 ** TRACE_BUFFER_CSR_MIN_ADDR_WIDTH, 
    localparam MCU_TRACE_BUFFER_START_ADDR      = 32'h0001_0000,
    localparam MCU_TRACE_BUFFER_END_ADDR        = MCU_TRACE_BUFFER_START_ADDR + (MCU_TRACE_BUFFER_SIZE_BYTES) - 1,
    localparam MBOX0_START_ADDR                 = 32'h0020_0000,
    localparam MBOX0_END_ADDR                   = MBOX0_START_ADDR + ((32'h0000_0001 << MCU_MBOX_CSR_ADDR_WIDTH) - 1),
    localparam MBOX1_START_ADDR                 = 32'h0060_0000,
    localparam MBOX1_END_ADDR                   = MBOX1_START_ADDR + ((32'h0000_0001 << MCU_MBOX_CSR_ADDR_WIDTH) - 1),
    localparam MCU_SRAM_START_ADDR              = 32'h00A0_0000,
    localparam MCU_SRAM_END_ADDR                = MCU_SRAM_START_ADDR + (MCU_SRAM_SIZE_KB * KB) - 1, 
      
    localparam MCI_END_ADDR   = MCU_SRAM_END_ADDR,
    localparam MCI_INTERNAL_ADDR_WIDTH = $clog2(MCI_END_ADDR)
        
    )
    (
    input clk,
    input rst_b,

    //SOC inf
    cif_if.response  soc_resp_if,

    //MCI REG inf
    cif_if.request  mci_reg_req_if, 

    //MCU SRAM inf
    cif_if.request  mcu_sram_req_if,

    //MCU Trace Buffer inf
    cif_if.request  mcu_trace_buffer_req_if,

    //MCI Mbox0 inf
    cif_if.request  mcu_mbox0_req_if,

    // Mbox1 SRAM Interface
    cif_if.request  mcu_mbox1_req_if,

    // Privileged requests 
    output logic axi_mcu_lsu_req,
    output logic axi_mcu_ifu_req,
    output logic axi_mcu_req    ,
    output logic axi_mci_soc_config_req    ,
    output logic axi_mcu_sram_config_req    ,

    
    // Privileged AXI users
    input logic [$bits(soc_resp_if.req_data.user)-1:0] strap_mcu_lsu_axi_user,
    input logic [$bits(soc_resp_if.req_data.user)-1:0] strap_mcu_ifu_axi_user,
    input logic [$bits(soc_resp_if.req_data.user)-1:0] strap_mcu_sram_config_axi_user,
    input logic [$bits(soc_resp_if.req_data.user)-1:0] strap_mci_soc_config_axi_user
);


// GRANT signals
logic soc_mcu_sram_gnt;
logic soc_mcu_trace_buffer_gnt;
logic soc_mci_reg_gnt;
logic soc_mcu_mbox0_gnt;
logic soc_mcu_mbox1_gnt;

// REQ signals
logic soc_mcu_sram_req;
logic soc_mcu_trace_buffer_req;
logic soc_mci_reg_req;
logic soc_mcu_mbox0_req;
logic soc_mcu_mbox1_req;

// MISC signals
logic soc_req_miss;
logic mci_soc_config_req_disable;
logic mci_soc_config_req_force_enable;
logic mci_soc_config_axi_user_detect;


///////////////////////////////////////////////////////////
// Decode which address space is being requested
///////////////////////////////////////////////////////////
//SoC requests to MCU_SRAM
always_comb soc_mcu_sram_gnt = (soc_resp_if.dv & (soc_resp_if.req_data.addr[MCI_INTERNAL_ADDR_WIDTH-1:0] inside {[MCU_SRAM_START_ADDR:MCU_SRAM_END_ADDR]}));

// SoC request to MCU Trace Buffer
always_comb soc_mcu_trace_buffer_gnt = (soc_resp_if.dv & (soc_resp_if.req_data.addr[MCI_INTERNAL_ADDR_WIDTH-1:0] inside {[MCU_TRACE_BUFFER_START_ADDR:MCU_TRACE_BUFFER_END_ADDR]}));

// SoC request to MCI Reg
always_comb soc_mci_reg_gnt = (soc_resp_if.dv & (soc_resp_if.req_data.addr[MCI_INTERNAL_ADDR_WIDTH-1:0] inside {[MCI_REG_START_ADDR:MCI_REG_END_ADDR]}));

// SoC request to MCI Mbox0
always_comb soc_mcu_mbox0_gnt = (soc_resp_if.dv & (soc_resp_if.req_data.addr[MCI_INTERNAL_ADDR_WIDTH-1:0] inside {[MBOX0_START_ADDR:MBOX0_END_ADDR]}));



// SoC request to MCI Mbox1
always_comb soc_mcu_mbox1_gnt = (soc_resp_if.dv & (soc_resp_if.req_data.addr[MCI_INTERNAL_ADDR_WIDTH-1:0] inside {[MBOX1_START_ADDR:MBOX1_END_ADDR]}));

///////////////////////////////////////////////////////////
// Add qualifiers to grant before sending to IPs
///////////////////////////////////////////////////////////

// MCU SRAM
always_comb soc_mcu_sram_req = soc_mcu_sram_gnt;

// MCU Trace Buffer
always_comb soc_mcu_trace_buffer_req = soc_mcu_trace_buffer_gnt;

// MCI REG 
always_comb soc_mci_reg_req   = soc_mci_reg_gnt;

// MCI Mbox0
always_comb soc_mcu_mbox0_req = soc_mcu_mbox0_gnt;

// MCI Mbox1
always_comb soc_mcu_mbox1_req = soc_mcu_mbox0_gnt;


///////////////////////////////////////////////////////////
// Drive DV to appropriate destination
///////////////////////////////////////////////////////////

// MCU SRAM
always_comb mcu_sram_req_if.dv = soc_mcu_sram_req;

// MCU TRACE BUFFER
always_comb mcu_trace_buffer_req_if.dv = soc_mcu_trace_buffer_req;

// MCI REG 
always_comb mci_reg_req_if.dv = soc_mci_reg_req;

// MCI Mbox0
always_comb mcu_mbox0_req_if.dv = soc_mcu_mbox0_req;

// MCI Mbox1
always_comb mcu_mbox1_req_if.dv = soc_mcu_mbox1_req;


///////////////////////////////////////////////////////////
// Drive data and reqest to approriate destination.
///////////////////////////////////////////////////////////

// MCU SRAM
always_comb mcu_sram_req_if.req_data = soc_resp_if.req_data;

// MCU TRACE BUFFER
always_comb mcu_trace_buffer_req_if.req_data = soc_resp_if.req_data;

// MCI REG 
always_comb mci_reg_req_if.req_data = soc_resp_if.req_data;

// MCI Mbox0
always_comb mcu_mbox0_req_if.req_data = soc_resp_if.req_data;

// MCI MBOX1
always_comb mcu_mbox1_req_if.req_data = soc_resp_if.req_data;


///////////////////////////////////////////////////////////
// Drive read data back
///////////////////////////////////////////////////////////

assign soc_resp_if.rdata =  soc_mcu_sram_req            ? mcu_sram_req_if.rdata : 
                            soc_mcu_trace_buffer_req    ? mcu_trace_buffer_req_if.rdata  :
                            soc_mci_reg_req             ? mci_reg_req_if.rdata  :
                            soc_mcu_mbox0_req           ? mcu_mbox0_req_if.rdata  :
                            soc_mcu_mbox1_req           ? mcu_mbox1_req_if.rdata  :
                            '0;




///////////////////////////////////////////////////////////
// Drive appropriate hold back
///////////////////////////////////////////////////////////

always_comb soc_resp_if.hold =  (soc_mcu_sram_req           & (~soc_mcu_sram_req | mcu_sram_req_if.hold)) |
                                (soc_mcu_trace_buffer_req   & (~soc_mcu_trace_buffer_req | mcu_trace_buffer_req_if.hold)) |
                                (soc_mci_reg_req            & (~soc_mci_reg_req | mci_reg_req_if.hold)) |
                                (soc_mcu_mbox0_req          & (~soc_mcu_mbox0_req | mcu_mbox0_req_if.hold)) |
                                (soc_mcu_mbox1_req          & (~soc_mcu_mbox1_req | mcu_mbox1_req_if.hold)) ;



///////////////////////////////////////////////////////////
// Drive appropriate error back or request misses all destinations
///////////////////////////////////////////////////////////

// Missed all destinations 
always_comb soc_req_miss = soc_resp_if.dv & ~(soc_mcu_sram_req | soc_mcu_trace_buffer_req | soc_mci_reg_req | soc_mcu_mbox0_req | soc_mcu_mbox1_req);

// Error for SOC
always_comb soc_resp_if.error = (soc_mcu_sram_req           & mcu_sram_req_if.error)  |
                                (soc_mcu_trace_buffer_req   & mcu_trace_buffer_req_if.error)   |
                                (soc_mci_reg_req            & mci_reg_req_if.error)   |
                                (soc_mcu_mbox0_req          & mcu_mbox0_req_if.error) |
                                (soc_mcu_mbox1_req          & mcu_mbox1_req_if.error) |
                                soc_req_miss;

///////////////////////////////////////////////
// Determine if the user matches any of the  
// privileged users
///////////////////////////////////////////////

// All 0s disabled mci_soc_config_axi user capability. Mutually exclusive with
// debug_req_force_enable.
assign mci_soc_config_req_disable = ~|strap_mci_soc_config_axi_user;

// All 1s every AXI transaction is treated as a debug user. Mutually exclusive
// with debug_req_disable
assign mci_soc_config_req_force_enable = &strap_mci_soc_config_axi_user;

assign mci_soc_config_axi_user_detect = ~(|(soc_resp_if.req_data.user ^ strap_mci_soc_config_axi_user));

assign axi_mci_soc_config_req    = soc_resp_if.dv & ((mci_soc_config_axi_user_detect & ~mci_soc_config_req_disable) | mci_soc_config_req_force_enable);

assign axi_mcu_lsu_req  = soc_resp_if.dv & ~(|(soc_resp_if.req_data.user ^ strap_mcu_lsu_axi_user));
assign axi_mcu_ifu_req  = soc_resp_if.dv & ~(|(soc_resp_if.req_data.user ^ strap_mcu_ifu_axi_user));
assign axi_mcu_req      = axi_mcu_lsu_req | axi_mcu_ifu_req; 

assign axi_mcu_sram_config_req      = soc_resp_if.dv & ~(|(soc_resp_if.req_data.user ^ strap_mcu_sram_config_axi_user));

///////////////////////////////////////////////
// Assertions 
///////////////////////////////////////////////
// One target per transaction
`CALIPTRA_ASSERT_MUTEX(ERR_MCI_AXI_AGENT_GRANT_MUTEX, {soc_mcu_sram_gnt, soc_mcu_trace_buffer_gnt, soc_mci_reg_gnt, soc_mcu_mbox0_gnt, soc_mcu_mbox1_gnt}, clk, !reset_n)

// Verify no overlapping address spaces. Only checking abutting address paces.
`CALIPTRA_ASSERT_INIT(ERR_AXI_ADDR_CHECK_MCI_REG, MCI_REG_END_ADDR < MCU_TRACE_BUFFER_START_ADDR)
`CALIPTRA_ASSERT_INIT(ERR_AXI_ADDR_CHECK_MCI_MCU_TRACE_BUFFER, MCU_TRACE_BUFFER_END_ADDR < MBOX0_START_ADDR)
`CALIPTRA_ASSERT_INIT(ERR_AXI_ADDR_CHECK_MCU_MBOX0, MBOX0_END_ADDR < MBOX1_START_ADDR)
`CALIPTRA_ASSERT_INIT(ERR_AXI_ADDR_CHECK_MCU_MBOX1, MBOX1_END_ADDR < MCU_SRAM_START_ADDR)

endmodule
