
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

module mci_axi_sub_decode 
    import mci_pkg::*;
    import mci_reg_pkg::*;
    #(
    // Configurable memory blocks
    parameter MCU_SRAM_SIZE_KB = 1024,
    parameter MBOX0_SIZE_KB    = 4, // KB
    parameter MBOX1_SIZE_KB    = 4, // KB


    ///////////////////////////////////////////////////////////
    // MCI Memory Map
    ///////////////////////////////////////////////////////////
    localparam MCI_REG_SIZE_BYTES    = 2 ** MCI_REG_MIN_ADDR_WIDTH, 
    localparam MCI_REG_START_ADDR    = 32'h0000_0000,
    localparam MCI_REG_END_ADDR      = MCI_REG_START_ADDR + (MCI_REG_SIZE_BYTES) - 1,
    localparam MBOX0_START_ADDR      = 32'h0008_0000,
    localparam MBOX0_END_ADDR        = MBOX0_START_ADDR + (MBOX0_SIZE_KB * KB) - 1,
    localparam MBOX1_START_ADDR      = MBOX0_END_ADDR + 32'h0000_0001, // FIXME: Do we want B2B
    localparam MBOX1_END_ADDR        = MBOX1_START_ADDR + (MBOX1_SIZE_KB * KB) - 1,
    localparam MCU_SRAM_START_ADDR   = 32'h0020_0000, // REQUIRED TO BE LAST ADDRESS IN MCI ADDRESS RANGE
    localparam MCU_SRAM_END_ADDR     = MCU_SRAM_START_ADDR + (MCU_SRAM_SIZE_KB * KB) - 1, 

    localparam MCI_END_ADDR   = MCU_SRAM_END_ADDR,
    localparam MCI_INTERNAL_ADDR_WIDTH = $clog2(MCI_END_ADDR)
        
    )
    (



    //SOC inf
    cif_if.response  soc_resp_if,

    //MCI REG inf
    cif_if.request  mci_reg_req_if, 

    //MCU SRAM inf
    cif_if.request  mcu_sram_req_if,

    // Privileged requests 
    output logic mcu_lsu_req,
    output logic mcu_ifu_req,
    output logic mcu_req    ,
    output logic clp_req    ,
    output logic soc_req    ,

    
    // Privileged AXI users
    input logic [soc_resp_if.USER_WIDTH-1:0] strap_mcu_lsu_axi_user,
    input logic [soc_resp_if.USER_WIDTH-1:0] strap_mcu_ifu_axi_user,
    input logic [soc_resp_if.USER_WIDTH-1:0] strap_clp_axi_user
);

// GRANT signals
logic soc_mcu_sram_gnt;
logic soc_mci_reg_gnt;


// MISC signals
logic soc_req_miss;


///////////////////////////////////////////////////////////
// Decode which address space is being requested
///////////////////////////////////////////////////////////
//SoC requests to MCU_SRAM
always_comb soc_mcu_sram_gnt = (soc_resp_if.dv & (soc_resp_if.req_data.addr[MCI_INTERNAL_ADDR_WIDTH-1:0] inside {[MCU_SRAM_START_ADDR:MCU_SRAM_END_ADDR]}));

// SoC request to MCI Reg
always_comb soc_mci_reg_gnt = (soc_resp_if.dv & (soc_resp_if.req_data.addr[MCI_INTERNAL_ADDR_WIDTH-1:0] inside {[MCI_REG_START_ADDR:MCI_REG_END_ADDR]}));


///////////////////////////////////////////////////////////
// Drive DV to appropriate destination
///////////////////////////////////////////////////////////

// MCU SRAM
always_comb mcu_sram_req_if.dv = soc_mcu_sram_gnt;

// MCI REG 
always_comb mci_reg_req_if.dv = soc_mci_reg_gnt;


///////////////////////////////////////////////////////////
// Drive data and reqest to approriate destination.
///////////////////////////////////////////////////////////

// MCU SRAM
always_comb mcu_sram_req_if.req_data = soc_resp_if.req_data;

// MCI REG 
always_comb mci_reg_req_if.req_data = soc_resp_if.req_data;




///////////////////////////////////////////////////////////
// Drive read data back
///////////////////////////////////////////////////////////

assign soc_resp_if.rdata =  soc_mcu_sram_gnt    ? mcu_sram_req_if.rdata : 
                            soc_mci_reg_gnt     ? mci_reg_req_if.rdata  :
                            '0;




///////////////////////////////////////////////////////////
// Drive appropriate hold back
///////////////////////////////////////////////////////////

always_comb soc_resp_if.hold =  (soc_mcu_sram_gnt & (~soc_mcu_sram_gnt | mcu_sram_req_if.hold)) |
                                (soc_mci_reg_gnt & (~soc_mci_reg_gnt | mci_reg_req_if.hold));



///////////////////////////////////////////////////////////
// Drive appropriate error back or request misses all destinations
///////////////////////////////////////////////////////////

// Missed all destinations 
always_comb soc_req_miss = soc_resp_if.dv & ~(soc_mcu_sram_gnt | soc_mci_reg_gnt);

// Error for SOC
always_comb soc_resp_if.error = (soc_mcu_sram_gnt & mcu_sram_req_if.error) |
                                (soc_mci_reg_gnt  & mci_reg_req_if.error)  |
                                soc_req_miss;

///////////////////////////////////////////////
// Determine if the user matches any of the  
// privileged users
///////////////////////////////////////////////

assign mcu_lsu_req  = soc_resp_if.dv & ~(|(soc_resp_if.req_data.user ^ strap_mcu_lsu_axi_user));
assign mcu_ifu_req  = soc_resp_if.dv & ~(|(soc_resp_if.req_data.user ^ strap_mcu_ifu_axi_user));
assign mcu_req      = mcu_lsu_req | mcu_ifu_req; 

assign clp_req      = soc_resp_if.dv & ~(|(soc_resp_if.req_data.user ^ strap_clp_axi_user));

assign soc_req      = soc_resp_if.dv & ~(mcu_req | clp_req);


endmodule
