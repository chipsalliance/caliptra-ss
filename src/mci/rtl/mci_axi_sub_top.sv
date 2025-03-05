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
//      Translates AXI requests to internal fabric. Decoding the requests
//      and sending to the appropriate target.
//


module mci_axi_sub_top 
    #(
    parameter AXI_ADDR_WIDTH    = 32,
    parameter AXI_DATA_WIDTH    = 32,
    parameter AXI_USER_WIDTH    = 32,
    parameter AXI_ID_WIDTH      = 8,
    parameter MCU_SRAM_SIZE_KB  = 512
    )
    (
    input logic clk,

    // MCI Resets
    input logic rst_b,

    // MCI AXI Interface
    axi_if.w_sub s_axi_w_if,
    axi_if.r_sub s_axi_r_if,

    // MCI reg Interface
    cif_if.request  mci_reg_req_if,

    // MCU SRAM Interface
    cif_if.request  mcu_sram_req_if,
    
    // MCU Trace Buffer Interface
    cif_if.request  mcu_trace_buffer_req_if,

    // Mbox0 SRAM Interface
    cif_if.request  mci_mbox0_req_if,
    input logic [4:0][$bits(s_axi_w_if.aruser)-1:0] valid_mbox0_users,

    // Mbox1 SRAM Interface
    cif_if.request  mci_mbox1_req_if,
    input logic [4:0][$bits(s_axi_w_if.aruser)-1:0] valid_mbox1_users,


    // Privileged requests 
    output logic axi_mci_soc_config_req,
    output logic axi_mcu_lsu_req,
    output logic axi_mcu_ifu_req,
    output logic axi_mcu_req    ,
    output logic axi_mcu_sram_config_req    ,

    
    // Privileged AXI users
    input logic [$bits(s_axi_w_if.aruser)-1:0] strap_mci_soc_config_axi_user,
    input logic [$bits(s_axi_w_if.aruser)-1:0] strap_mcu_lsu_axi_user,
    input logic [$bits(s_axi_w_if.aruser)-1:0] strap_mcu_ifu_axi_user,
    input logic [$bits(s_axi_w_if.aruser)-1:0] strap_mcu_sram_config_axi_user
    );


// Interface between axi_sub and mci decoder
cif_if #(
    .ADDR_WIDTH(AXI_ADDR_WIDTH), 
    .DATA_WIDTH(AXI_DATA_WIDTH), 
    .ID_WIDTH(AXI_ID_WIDTH),
    .USER_WIDTH(AXI_USER_WIDTH)
    )
    soc_resp_if(
        .clk,
        .rst_b(rst_b)
    );

//AXI Interface
//This module contains the logic for interfacing with the SoC over the AXI Interface
//The SoC sends read and write requests using AXI Protocol
//This wrapper decodes that protocol, collapses the full-duplex protocol to
// simplex, and issues requests to the MIC decode block
axi_sub #(
    .AW   (AXI_ADDR_WIDTH),
    .DW   (AXI_DATA_WIDTH),
    .UW   (AXI_USER_WIDTH),
    .IW   (AXI_ID_WIDTH  ),
    .EX_EN(0             ),
    .C_LAT(0             )
) i_axi_sub (
    .clk,
    .rst_n(rst_b), 

    // AXI INF
    .s_axi_w_if,
    .s_axi_r_if,


    //COMPONENT INF
    .dv    (soc_resp_if.dv  ),
    .addr  (soc_resp_if.req_data.addr    ), // Byte address
    .write (soc_resp_if.req_data.write   ),
    .user  (soc_resp_if.req_data.user    ), 
    .id    (soc_resp_if.req_data.id      ),
    .wdata (soc_resp_if.req_data.wdata   ), // Requires: Component dwidth == AXI dwidth
    .wstrb (soc_resp_if.req_data.wstrb   ), 
    .rdata (soc_resp_if.rdata   ), // Requires: Component dwidth == AXI dwidth
    .last  (soc_resp_if.req_data.last), 
    .hld   (soc_resp_if.hold    ),
    .rd_err(soc_resp_if.error   ),
    .wr_err(soc_resp_if.error   )
);

assign soc_resp_if.req_data.size = '0; 

//AXI Interface
//This module contains the logic for interfacing with the SoC over the AXI Interface
//The SoC sends read and write requests using AXI Protocol
//This wrapper decodes that protocol, collapses the full-duplex protocol to
// simplex, and issues requests to the MIC decode block
mci_axi_sub_decode #(
    .MCU_SRAM_SIZE_KB   (MCU_SRAM_SIZE_KB)
) i_mci_axi_sub_decode (
    .clk,
    .rst_b,

    //SOC inf
    .soc_resp_if        (soc_resp_if.response),

    //MCI reg inf
    .mci_reg_req_if,

    //MCU SRAM inf
    .mcu_sram_req_if,
    
    //MCU Trace Buffer inf
    .mcu_trace_buffer_req_if,

    //MCI Mbox0
    .mci_mbox0_req_if,
    .valid_mbox0_users,

    //MCI Mbox1
    .mci_mbox1_req_if,
    .valid_mbox1_users,

    // Privileged requests 
    .axi_mci_soc_config_req,
    .axi_mcu_lsu_req,
    .axi_mcu_ifu_req,
    .axi_mcu_req    ,
    .axi_mcu_sram_config_req    ,

    
    // Privileged AXI users
    .strap_mci_soc_config_axi_user,
    .strap_mcu_lsu_axi_user,
    .strap_mcu_ifu_axi_user,
    .strap_mcu_sram_config_axi_user

);


endmodule
