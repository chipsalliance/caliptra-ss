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
//      This module is used to control requests going to a single MCU SRAM.
//      Requests come in through the cif_resp_if and are passed the the SRAM
//      on the mci_mcu_sram_req_if. 
//
//      Fabric Limitations:
//      The integrator and higher level fabric is responsible for routing appropriate 
//      requests to the MCU SRAM as this module cannot detect address aliasing.
//
//      Error handling:
//      If an access violation due to USER privilege issues is detected it 
//      will always return an error on the first cycle of the cif_if.
//      ECC errors are returned on the read data phase (second clock cycle)
//
//      Region mapping:
//      The lower address is mapped to the exec region. Upper address range is mapped
//      to prot region. If fw_sram_exec_region_size is larger than the actual SRAM size 
//      the entire SRAM is considered exec region and there is no prot region
`include "caliptra_sva.svh"


module mci_mcu_sram_ctrl 
    #(
    parameter  MCU_SRAM_SIZE_KB = 512
    ,parameter  MCU_SRAM_DMI_ADDR_ADDR = 7'h58
    ,parameter  MCU_SRAM_DMI_DATA_ADDR = 7'h59
    ,localparam BITS_IN_BYTE = 8
    ,localparam KB = 1024 // Bytes in KB

    ,localparam MCU_SRAM_SIZE_BYTES = MCU_SRAM_SIZE_KB * KB
    ,localparam MCU_SRAM_DATA_W = 32 // ECC not parametrized so can't expose this parameter
    ,localparam MCU_SRAM_DATA_W_BYTES = MCU_SRAM_DATA_W / BITS_IN_BYTE
    ,localparam MCU_SRAM_ECC_DATA_W = 7 // ECC not parameterized so can't expose this parameter
    ,localparam MCU_SRAM_DATA_AND_ECC_W = MCU_SRAM_DATA_W + MCU_SRAM_ECC_DATA_W
    ,localparam MCU_SRAM_DEPTH = MCU_SRAM_SIZE_BYTES / MCU_SRAM_DATA_W_BYTES
    ,localparam MCU_SRAM_ADDR_W = $clog2(MCU_SRAM_DEPTH)

    // Number of address bits needed on cif_req_if.addr to address the entire 
    // SRAM. AKA address scope
    ,localparam MCU_SRAM_CIF_ADDR_W = $clog2(MCU_SRAM_SIZE_BYTES)
    )
    (
    input logic clk,

    // MCI Resets
    input logic rst_b,
    input logic mci_pwrgood,

    // MCU Reset
    input logic mcu_rst_b,

    // Interface
    input logic [15:0] fw_sram_exec_region_size, // 4KB steps with 0 being 4KB

    // Caliptra internal fabric response interface
    cif_if.response  cif_resp_if,

    // Debug mode
    input debug_en,

    // AXI Privileged requests
    input logic axi_mcu_lsu_req,
    input logic axi_mcu_ifu_req,
    input logic axi_mcu_sram_config_req ,


    // Access lock interface
    input logic mcu_sram_fw_exec_region_lock,

    // Error Status
    output logic sram_single_ecc_error,
    output logic sram_double_ecc_error,
    output logic dmi_axi_collision_error,

    // DMI
    input  logic        dmi_uncore_en,
    input  logic        dmi_uncore_wr_en,
    input  logic [ 6:0] dmi_uncore_addr,
    input  logic [31:0] dmi_uncore_wdata,
    output logic [31:0] dmi_uncore_rdata,


    // Interface with SRAM
    mci_mcu_sram_if.request mci_mcu_sram_req_if


);

// Memory protection controls
logic fw_exec_region_mcu_access;

// Memory region request
logic exec_region_match;
logic exec_region_req;
logic prot_region_req;

// Memory region mapping
logic [28:0]                    exec_region_base; // TODO: Report to status register?
logic [28:0]                    exec_region_end_calc;  
logic [28:0]                    exec_region_end;  // TODO: Report to status register?
logic                           exec_region_overflow;
// fw_sram_exec_region_size size is 16 bits so the max size 
// the exec region can be is (0xFFF + 1) << 12 =  10_000_000
// Which bit 28 set.
logic [28:0] exec_region_size_bytes;



// Filtering status
logic exec_region_filter_success;
logic exec_region_filter_error; 

logic prot_region_filter_success;
logic prot_region_filter_error; 



// SRAM Read/Write request signals
logic mcu_sram_valid_req;
logic mcu_sram_read_req;
logic mcu_sram_write_req;
logic mcu_sram_rmw_req;
logic mcu_sram_rmw_read_req; 
logic mcu_sram_rmw_write_req; 
logic sram_req;
logic sram_read_req;
logic sram_write_req;
logic sram_read_data_avail;
logic mcu_sram_req_second_cycle;

// SRAM read/ecc
logic sram_rd_ecc_en;
logic [MCU_SRAM_DATA_W-1:0] sram_rdata;
logic [MCU_SRAM_DATA_W-1:0] sram_rmw_wdata;
logic [MCU_SRAM_DATA_W-1:0] sram_rdata_cor;
logic [MCU_SRAM_ECC_DATA_W-1:0] sram_rdata_ecc;

// DMI           
logic mcu_sram_dmi_addr_req;
logic mcu_sram_dmi_data_req;
logic mcu_sram_dmi_addr_wr_req ;
logic mcu_sram_dmi_addr_wr_req_f ;
logic mcu_sram_dmi_data_wr_req ;
logic mcu_sram_dmi_addr_rd_req ;
logic mcu_sram_dmi_data_rd_req ;
logic mcu_sram_dmi_req;
logic [MCU_SRAM_ADDR_W-1:0] mcu_sram_dmi_addr_reg;
logic [MCU_SRAM_DATA_W-1:0] mcu_sram_dmi_data_reg;

// MISC
logic axi_debug_req_qual;

///////////////////////////////////////////////
// DMI Register IF
///////////////////////////////////////////////

// Address decode
assign mcu_sram_dmi_addr_req = (dmi_uncore_en && (dmi_uncore_addr == MCU_SRAM_DMI_ADDR_ADDR));
assign mcu_sram_dmi_data_req = (dmi_uncore_en && (dmi_uncore_addr == MCU_SRAM_DMI_DATA_ADDR));

// Write request
assign mcu_sram_dmi_addr_wr_req = mcu_sram_dmi_addr_req && dmi_uncore_wr_en;
assign mcu_sram_dmi_data_wr_req = mcu_sram_dmi_data_req && dmi_uncore_wr_en;

// Read request
assign mcu_sram_dmi_addr_rd_req = mcu_sram_dmi_addr_req && ~dmi_uncore_wr_en ;
assign mcu_sram_dmi_data_rd_req = mcu_sram_dmi_data_req && ~dmi_uncore_wr_en ;

assign mcu_sram_dmi_req = mcu_sram_dmi_data_wr_req | mcu_sram_dmi_data_rd_req;

// DMI ADDR Reg
always_ff @ (posedge clk or negedge mci_pwrgood) begin
    if(!mci_pwrgood) begin
        mcu_sram_dmi_addr_reg <= '0;
    end
    else begin
        if(mcu_sram_dmi_addr_wr_req) begin
            mcu_sram_dmi_addr_reg <= dmi_uncore_wdata[MCU_SRAM_ADDR_W-1:0];
        end
    end
end

// DMI Read regs
always_ff @ (posedge clk or negedge mci_pwrgood) begin
    if(!mci_pwrgood) begin
        mcu_sram_dmi_addr_wr_req_f <= '0;
        mcu_sram_dmi_data_reg <= '0;
    end
    else begin
        mcu_sram_dmi_addr_wr_req_f <= mcu_sram_dmi_addr_wr_req;

        if(mcu_sram_dmi_addr_wr_req_f) begin
            mcu_sram_dmi_data_reg <= sram_rdata_cor;
        end
    end
end


assign dmi_uncore_rdata = mcu_sram_dmi_addr_rd_req ? { {32-MCU_SRAM_ADDR_W{1'b0}}, mcu_sram_dmi_addr_reg} : 
                          mcu_sram_dmi_data_rd_req ? mcu_sram_dmi_data_reg : 
                          '0;
                          
// Collision only if accessing DMI data since DMI addr doesn't send
// a request to the SRAM
assign dmi_axi_collision_error = cif_resp_if.dv & mcu_sram_dmi_data_req;

///////////////////////////////////////////////
// Calculate all properties about the SRAM 
// based on the fw_sram_exec_region_size
///////////////////////////////////////////////
assign exec_region_base = '0;
// 4KB = 2^12
assign exec_region_size_bytes   = {13'b0, (fw_sram_exec_region_size + 16'b1)} << 12; 
// Calculate final address based on the fw_sram_exec_region_size.
assign exec_region_end_calc     = exec_region_base + exec_region_size_bytes - 1;
// Check if there was overflow due to fw_sram_exec_region_size being larger than the entire
// SRAM.
assign exec_region_overflow  = |exec_region_end_calc[28:MCU_SRAM_CIF_ADDR_W];
// If there was overflow set to the MCU SRAM size.
// Otherwise take the calculated value
assign exec_region_end  = exec_region_overflow ? (MCU_SRAM_SIZE_BYTES-1) : 
                            exec_region_end_calc;  





///////////////////////////////////////////////
// Determine if protected region or execution
// region is being accessed
///////////////////////////////////////////////

// Detect if the address in the MCU_SRAM scope matches the exec region 
// When determining the exec_region_end it must address overflow/over provision 
// issues for this check to work.
assign exec_region_match =  (cif_resp_if.req_data.addr[MCU_SRAM_CIF_ADDR_W-1:0] <= exec_region_end[MCU_SRAM_CIF_ADDR_W-1:0]);

// Qualify the exec_region_match with DV to detect either exec or prot
// region request
assign exec_region_req = cif_resp_if.dv & exec_region_match;
assign prot_region_req = cif_resp_if.dv & !exec_region_match; 


///////////////////////////////////////////////
// Protected data region access protection  
///////////////////////////////////////////////

// When debug enabled allow full access to the SRAM
assign axi_debug_req_qual = cif_resp_if.dv & debug_en;

// This logic will help in 2 areas:
// 1. We can use these signals to block read or a write
//    ever reaching the SRAM.
// 2. Reads take 2 clock cycles. But we can use these signals
//    to detect an illegal access and respond with an error 
//    on the first clock cycle
assign prot_region_filter_success = prot_region_req & (axi_mcu_lsu_req | axi_debug_req_qual);
assign prot_region_filter_error   = prot_region_req & ~prot_region_filter_success;


///////////////////////////////////////////////
// Execution data region access protection  
///////////////////////////////////////////////

// Cannot directly use the mcu_sram_fw_exec_region_lock
// because when cleared MCU could still be executing
// from MCU SRAM. We need to make sure MCU is in reset
// before we switch access from MCU -> Caliptra
always_ff @(posedge clk or negedge rst_b) begin
    if(!rst_b) begin
        fw_exec_region_mcu_access <= '0;
    end
    else begin
        if (mcu_sram_fw_exec_region_lock) begin
            fw_exec_region_mcu_access <= 1'b1;
        end
        else if(!mcu_rst_b) begin
            fw_exec_region_mcu_access <= 1'b0;
        end
    end
end

// This logic will help in 2 areas:
// 1. We can use these signals to block read or a write
//    ever reaching the SRAM.
// 2. Reads take 2 clock cycles. But we can use these signals
//    to detect an illegal access and respond with an error 
//    on the first clock cycle
always_comb begin
    exec_region_filter_success = '0;
    exec_region_filter_error   = '0;
    if (exec_region_req) begin
        if (fw_exec_region_mcu_access) begin
            exec_region_filter_success = (axi_mcu_lsu_req | axi_mcu_ifu_req | axi_debug_req_qual);
            exec_region_filter_error   = ~exec_region_filter_success;
        end 
        else begin
            exec_region_filter_success = axi_mcu_sram_config_req | axi_debug_req_qual;
            exec_region_filter_error   = ~exec_region_filter_success;
        end
    end
end


///////////////////////////////////////////////
// Converting the CIF to memory request 
///////////////////////////////////////////////


//////////
// Additional control signal
//////////
// CIF read or write request has successfully passed all filtering 
// and the request needs to be sent to the SRAM
assign mcu_sram_valid_req = exec_region_filter_success | prot_region_filter_success;

// Detecting read, write , vs byte write (rmw) requests
assign mcu_sram_read_req  = mcu_sram_valid_req & (~cif_resp_if.req_data.write);

assign mcu_sram_write_req = mcu_sram_valid_req & cif_resp_if.req_data.write &   (&cif_resp_if.req_data.wstrb);

// Detects we need to do a RMW 
assign mcu_sram_rmw_req   = mcu_sram_valid_req & cif_resp_if.req_data.write & (~(&cif_resp_if.req_data.wstrb));
// Detects we are on the read phase of the RMW
assign mcu_sram_rmw_read_req = mcu_sram_rmw_req & ~mcu_sram_req_second_cycle; 
// Detects we are on the write phase of the RMW request a write if the data read back was valid.
assign mcu_sram_rmw_write_req = mcu_sram_rmw_req & mcu_sram_req_second_cycle & ~sram_double_ecc_error; 

// Transactions to SRAM can only be 1 clock cycle or 2. 2 clock cycles are needed for:
//  1: Read req
//  2: RMW req 
// Since it takes 1 clock cycles to read the data
always_ff @(posedge clk or negedge rst_b) begin
    if(!rst_b) begin
        mcu_sram_req_second_cycle <= '0;
    end
    else begin
        mcu_sram_req_second_cycle <= (mcu_sram_read_req | mcu_sram_rmw_req) & ~mcu_sram_req_second_cycle;
    end

end


// At this point we are translating the MCU SRAM requests into actual SRAM requests for the SRAM interface
// MCU SRAM read and write only have 1 request.
// MCU SRAM RMW have 2 requests
assign sram_req = ((mcu_sram_read_req | mcu_sram_write_req | mcu_sram_dmi_data_wr_req | mcu_sram_dmi_addr_wr_req) & ~mcu_sram_req_second_cycle)  | (mcu_sram_rmw_req);

assign sram_write_req = sram_req & (mcu_sram_write_req | mcu_sram_rmw_write_req | mcu_sram_dmi_data_wr_req);
assign sram_read_req  = sram_req & (mcu_sram_read_req  | mcu_sram_rmw_read_req  | mcu_sram_dmi_addr_wr_req);


// Assumption is that in order for there to be a second cycle 
// there must have been a read to the SRAM.
assign sram_read_data_avail = mcu_sram_req_second_cycle;


//////////
// General Read/Write SRAM controls
//////////

// All these signals should only be asserted during sram_req
// otherwise when we do reads that require 2 clock cycles we will
// trigger a second read to the SRAM.

// All Txs we need to pass the address to the memory interface.
// Speculatively read the SRAM whenever we write the addr reg
// When writing the data reg, we use the latched address to write to the SRAM
// Must shift the address to account for sram being more than 1 byte wide 
assign mci_mcu_sram_req_if.req.addr = mcu_sram_dmi_addr_wr_req ? dmi_uncore_wdata[MCU_SRAM_ADDR_W-1:0] :
                                      mcu_sram_dmi_data_wr_req ? mcu_sram_dmi_addr_reg :
                                                      sram_req ? cif_resp_if.req_data.addr [MCU_SRAM_CIF_ADDR_W-1:2] : '0;

// All requests assert CS
assign mci_mcu_sram_req_if.req.cs = sram_req;


//////////
// Write SRAM controls
//////////

// Only toggle WE if write request
assign mci_mcu_sram_req_if.req.we    = sram_write_req; 

// RMW data
genvar i;
generate 
    for(i=0; i < $bits(cif_resp_if.req_data.wstrb); i = i + 1) begin : gen_rmw_data_mask
        assign sram_rmw_wdata[i*8 +: 8] = cif_resp_if.req_data.wstrb[i] ? cif_resp_if.req_data.wdata[i*8 +: 8] : sram_rdata_cor[i*8 +: 8];
    end
endgenerate

// Only passing write data to SRAM if write request.
always_comb begin
    mci_mcu_sram_req_if.req.wdata.data = '0;
    if(sram_write_req) begin
        if(mcu_sram_rmw_req) begin
            mci_mcu_sram_req_if.req.wdata.data = sram_rmw_wdata;
        end
        else if (mcu_sram_dmi_data_wr_req) begin
            mci_mcu_sram_req_if.req.wdata.data = dmi_uncore_wdata;
        end
        else begin
            mci_mcu_sram_req_if.req.wdata.data = cif_resp_if.req_data.wdata;
        end
    end
end

// From RISC-V core beh_lib.sv
// 32-bit data width hardcoded
// 7-bit ECC width hardcoded
rvecc_encode ecc_encode (
    .din    ( mci_mcu_sram_req_if.req.wdata.data),
    .ecc_out( mci_mcu_sram_req_if.req.wdata.ecc )
);


//////////
// Read SRAM controls
//////////

assign sram_rd_ecc_en = sram_read_data_avail;

assign sram_rdata = mci_mcu_sram_req_if.resp.rdata.data;
assign sram_rdata_ecc = mci_mcu_sram_req_if.resp.rdata.ecc;

rvecc_decode ecc_decode (
    .en              (sram_rd_ecc_en       ),
    .sed_ded         ( 1'b0                ),    // 1 : means only detection
    .din             (sram_rdata           ),
    .ecc_in          (sram_rdata_ecc       ),
    .dout            (sram_rdata_cor       ),
    .ecc_out         (                     ), // Unused in today's design
    .single_ecc_error(sram_single_ecc_error), // TODO use to flag write-back
    .double_ecc_error(sram_double_ecc_error)  // TODO use to flag command error
);

// Only send data back if sram_read_data_avail and the request to mcu_ream was
// a read. There are reads to the SRAM when we get a RMW command meaning not all strb bits are set. 
// Assumptions made:
// 1. We will only have sram_read_data_avail if a privileged agent is doing the read
// 2. If an ECC error is detected it is OK to send garbage data back.
assign cif_resp_if.rdata = (sram_read_data_avail & mcu_sram_read_req) ?  sram_rdata_cor : '0;

///////////////////////////////////////////////
// Hold response 
///////////////////////////////////////////////

// Only hold up the interface if we have a successful 
// read request. Meaning the read request got through all
// the protection filtering and is sent to the SRAM. 
// We wait 1 clock cycle and then read data is back
// from the sram
assign cif_resp_if.hold = sram_read_req; 


///////////////////////////////////////////////
// Error response 
///////////////////////////////////////////////

// Anytime an error is detected we pass it back on the interface.
// All error sources in this module shall only assert when DV is asserted.
// This logic is just an aggregate of the error sources and will not check
// for DV.
assign cif_resp_if.error = exec_region_filter_error | 
                           prot_region_filter_error |
                           sram_double_ecc_error;  

// SRAM is single port and cannot handle reads and writes in the same clock cycle
`CALIPTRA_ASSERT_MUTEX(ERR_MCU_SRAM_MULTI_REQ, {sram_write_req, sram_read_req}, clk, !rst_b)

// SRAM ECC Errors
`CALIPTRA_ASSERT_NEVER(ERR_MCU_SRAM_ECC_DB_ERROR, sram_double_ecc_error, clk, !rst_b)
`CALIPTRA_ASSERT_NEVER(ERR_MCU_SRAM_ECC_SB_ERROR, sram_single_ecc_error, clk, !rst_b)

// SRAM protection errors
`CALIPTRA_ASSERT_NEVER(ERR_MCU_SRAM_EXEC_REGION_FILTER_ERROR, exec_region_filter_error, clk, !rst_b)
`CALIPTRA_ASSERT_NEVER(ERR_MCU_SRAM_PROT_REGION_FILTER_ERROR, prot_region_filter_error, clk, !rst_b)

endmodule
