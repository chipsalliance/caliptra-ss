
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
    #(
    // Configurable memory blocks
    parameter MCU_SRAM_SIZE_KB = 1024,
    parameter MBOX0_SIZE_KB    = 4, // KB
    parameter MBOX1_SIZE_KB    = 4, // KB


    ///////////////////////////////////////////////////////////
    // MCI Memory Map
    ///////////////////////////////////////////////////////////
    localparam CSR_SIZE_KB           = 512, // FIXME should I expose? KB
    localparam CSR_START_ADDR        = 32'h0000_0000,
    localparam CSR_END_ADDR          = CSR_START_ADDR + (CSR_SIZE_KB * KB) - 1,
    localparam MBOX0_START_ADDR      = 32'h0008_0000,
    localparam MBOX0_END_ADDR        = MBOX0_START_ADDR + (MBOX0_SIZE_KB * KB) - 1,
    localparam MBOX1_START_ADDR      = MBOX0_END_ADDR + 32'h0000_0001, // FIXME: Do we want B2B
    localparam MBOX1_END_ADDR        = MBOX1_START_ADDR + (MBOX1_SIZE_KB * KB) - 1,
    localparam MCU_SRAM_START_ADDR   = 32'h0002_0000,
    localparam MCU_SRAM_END_ADDR     = MCU_SRAM_START_ADDR + (MCU_SRAM_SIZE_KB * KB) - 1

        
    )
    (
    //SOC inf
    cif_if.response  soc_resp_if,

    //MCU SRAM inf
    cif_if.request  mcu_sram_req_if 
);

// GRANT signals
logic soc_mcu_sram_gnt;

// MISC signals
logic soc_req_miss;


///////////////////////////////////////////////////////////
// Decode which address space is being requested
///////////////////////////////////////////////////////////
//SoC requests to MCU_SRAM
always_comb soc_mcu_sram_gnt = (soc_resp_if.dv & (soc_resp_if.req_data.addr inside {[MCU_SRAM_START_ADDR:MCU_SRAM_END_ADDR]}));


///////////////////////////////////////////////////////////
// Drive DV to appropriate destination
///////////////////////////////////////////////////////////

// MCU SRAM
always_comb mcu_sram_req_if.dv = soc_mcu_sram_gnt;


///////////////////////////////////////////////////////////
// Drive data and reqest to approriate destination.
///////////////////////////////////////////////////////////

// MCU SRAM
always_comb mcu_sram_req_if.req_data = soc_resp_if.req_data;



///////////////////////////////////////////////////////////
// Drive read data back
///////////////////////////////////////////////////////////

assign soc_resp_if.rdata = soc_mcu_sram_gnt ? mcu_sram_req_if.rdata : '0;


///////////////////////////////////////////////////////////
// Drive approriate hold back
///////////////////////////////////////////////////////////

always_comb soc_resp_if.hold = (soc_mcu_sram_gnt & (~soc_mcu_sram_gnt | mcu_sram_req_if.hold));


///////////////////////////////////////////////////////////
// Drive approriate error back or request misses all desitnations
///////////////////////////////////////////////////////////

// Missed all destinations 
always_comb soc_req_miss = soc_resp_if.dv & ~(soc_mcu_sram_gnt);

// Error for SOC
always_comb soc_resp_if.error = (soc_mcu_sram_gnt & mcu_sram_req_if.error) |
                        soc_req_miss;

endmodule
