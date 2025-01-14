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


module mci_mcu_sram_ctrl 
    #(
    parameter  MCU_SRAM_SIZE_KB = 1024
    )
    (
    input logic clk,

    // MCI Resets
    input logic rst_b,

    // MCU Reset
    input logic mcu_rst_b,

    // Interface
    input logic [15:0] fw_sram_exec_region_size, // 4KB steps with 0 being 4KB

    // Caliptra internal fabric response interface
    cif_if.response  cif_resp_if,

    // AXI Privileged requests
    input logic mcu_lsu_req,
    input logic mcu_ifu_req,
    input logic clp_req ,


    // Access lock interface
    input logic mcu_sram_fw_exec_region_lock,

    // ECC Status
    output logic sram_single_ecc_error,
    output logic sram_double_ecc_error,


    // Interface with SRAM
    mci_mcu_sram_if.request mci_mcu_sram_req_if


);
localparam BITS_IN_BYTE = 8;
localparam KB = 1024; // Bytes in KB

localparam MCU_SRAM_SIZE_BYTES = MCU_SRAM_SIZE_KB * KB;
localparam MCU_SRAM_DATA_W = mci_mcu_sram_req_if.DATA_WIDTH;
localparam MCU_SRAM_DATA_W_BYTES = MCU_SRAM_DATA_W / BITS_IN_BYTE;
localparam MCU_SRAM_ECC_DATA_W = mci_mcu_sram_req_if.ECC_WIDTH;
localparam MCU_SRAM_DATA_AND_ECC_W = MCU_SRAM_DATA_W + MCU_SRAM_ECC_DATA_W;
localparam MCU_SRAM_DEPTH = MCU_SRAM_SIZE_BYTES / MCU_SRAM_DATA_W_BYTES;
localparam MCU_SRAM_ADDR_W = $clog2(MCU_SRAM_DEPTH);

// Number of address bits needed on cif_req_if.addr to address the entire 
// SRAM. AKA address scope
localparam MCU_SRAM_CIF_ADDR_W = $clog2(MCU_SRAM_SIZE_BYTES);

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



// SRAM Read/Write request and phase signals
logic mcu_sram_valid_req;
logic mcu_sram_read_req;
logic mcu_sram_write_req;
logic sram_req_phase;
logic sram_read_req_phase;
logic sram_write_req_phase;
logic sram_read_data_phase;

// SRAM read/ecc
logic sram_rd_ecc_en;
logic [MCU_SRAM_DATA_W-1:0] sram_rdata;
logic [MCU_SRAM_DATA_W-1:0] sram_rdata_cor;
logic [MCU_SRAM_ECC_DATA_W-1:0] sram_rdata_ecc;

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

// This logic will help in 2 areas:
// 1. We can use these signals to block read or a write
//    ever reaching the SRAM.
// 2. Reads take 2 clock cycles. But we can use these signals
//    to detect an illegal access and respond with an error 
//    on the first clock cycle
assign prot_region_filter_success = prot_region_req & mcu_lsu_req;
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
            exec_region_filter_success = (mcu_lsu_req | mcu_ifu_req);
            exec_region_filter_error   = ~exec_region_filter_success;
        end 
        else begin
            exec_region_filter_success = clp_req;
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

// Detecting read vs write requests
assign mcu_sram_read_req  = mcu_sram_valid_req & (~cif_resp_if.req_data.write);
assign mcu_sram_write_req = mcu_sram_valid_req & cif_resp_if.req_data.write;


// Reading the sram takes 2 clock cycles and write request only take
// 1 clock cycles
// 1 - req_phase: Request sent to SRAM to read an address
// 2 - data_phase: Data is read back from the SRAM. Not needed for write requests
assign sram_req_phase = mcu_sram_valid_req  & ~sram_read_data_phase; 

assign sram_write_req_phase = sram_req_phase & mcu_sram_write_req;
assign sram_read_req_phase = sram_req_phase & mcu_sram_write_req;

always_ff @(posedge clk or negedge rst_b) begin
    if(!rst_b) begin
        sram_read_data_phase <= '0;
    end
    else begin
        sram_read_data_phase <= (sram_req_phase & mcu_sram_read_req);
    end

end


//////////
// General Read/Write SRAM controls
//////////

// All these signals should only be asserted during the sram_req_phase
// otherwise when we do reads that require 2 clock cycles we will
// trigger a second read to the SRAM.

// Either read or write we need to pass the address to the memory interface.
// Must shift the address to account for sram being more than 1 byte wide 
assign mci_mcu_sram_req_if.req.addr = sram_req_phase ? cif_resp_if.req_data.addr [MCU_SRAM_ADDR_W-1:2] : '0;

// All requests assert CS
assign mci_mcu_sram_req_if.req.cs = sram_req_phase;


//////////
// Write SRAM controls
//////////

// Only toggle WE if write request
assign mci_mcu_sram_req_if.req.we    = sram_write_req_phase; 

// Only passing write data to SRAM if write request.
assign mci_mcu_sram_req_if.req.wdata.data = sram_write_req_phase ? cif_resp_if.req_data.wdata : '0;

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

assign sram_rd_ecc_en = sram_read_req_phase;

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

// Only send data back if we are in the sram_read_data_phase. Assumptions made:
// 1. We will only have sram_read_data_phase if a privileged agent is doing the read
// 2. If an ECC error is detected it is OK to send garbage data back.
assign cif_resp_if.rdata = sram_read_data_phase ?  sram_rdata_cor : '0;

///////////////////////////////////////////////
// Hold response 
///////////////////////////////////////////////

// Only hold up the interface if we have a successful 
// read request. Meaning the read request got through all
// the protection filtering and is sent to the SRAM. 
// We wait 1 clock cycle and then read data is back
// from the sram
assign cif_resp_if.hold = sram_read_req_phase; 


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



endmodule
