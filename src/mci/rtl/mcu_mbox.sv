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



module mcu_mbox 
    import mcu_mbox_csr_pkg::*;
    #(
    parameter  MCU_MBOX_SRAM_SIZE_KB = 512
    ,parameter DEF_MBOX_VALID_AXI_USER = 32'hFFFF_FFFF

    ,localparam BITS_IN_BYTE = 8
    ,localparam KB = 1024 // Bytes in KB
    ,localparam MCU_MBOX_SRAM_SIZE_BYTES = MCU_MBOX_SRAM_SIZE_KB * KB
    ,localparam MCU_MBOX_SRAM_DATA_W = 32 // ECC not parametrized so can't expose this parameter
    ,localparam MCU_MBOX_SRAM_DATA_W_BYTES = MCU_MBOX_SRAM_DATA_W / BITS_IN_BYTE
    ,localparam MCU_MBOX_SRAM_DEPTH = MCU_MBOX_SRAM_SIZE_BYTES / MCU_MBOX_SRAM_DATA_W_BYTES
    ,localparam MCU_MBOX_SRAM_ADDR_W = $clog2(MCU_MBOX_SRAM_DEPTH)


    )
    (
    input logic clk,

    // MCI Resets
    input logic rst_b,

    // Caliptra internal fabric response interface
    cif_if.response  cif_resp_if,

    input logic [$bits(cif_resp_if.req_data.user)-1:0]      strap_root_axi_user,

    // Mailbox valid users. 
    input logic [4:0][$bits(cif_resp_if.req_data.user)-1:0] valid_mbox_users,

    // Mailbox Status
    output logic soc_req_mbox_locked, // SoC user requested lock when root user has lock
    output logic root_mbox_data_available, // Root user set data available
    output logic soc_mbox_data_available,  // SoC user set data available
    output logic target_user_done,  // Target user status is ready

    // Mailbox SRAM ECC error flags
    output logic sram_single_ecc_error,
    output logic sram_double_ecc_error,

    mci_mcu_sram_if.request mcu_mbox_sram_req_if

);

mcu_mbox_csr__out_t hwif_out;
mcu_mbox_csr__in_t hwif_in;

logic mbox_valid_user;
logic mbox_valid_user_req;
logic mbox_valid_user_error;

logic csr_read_error;
logic csr_write_error;

logic valid_requester_req;
logic valid_root_req; 
logic valid_target_req;

logic mbox_target_user     ; 
logic mbox_requester_user  ; 
logic mbox_axi_root_user   ; 
logic mbox_target_user_req ; 
logic mbox_requester_user_req;
logic mbox_axi_root_user_req ;

logic lock_set;
logic valid_requester_target_req;

logic execute_prev;
logic mbox_sram_zero_done;
logic mbox_sram_zero_in_progress;

logic mbox_release;
logic sram_rd_ecc_en;
logic mbox_sram_rd_ack;
logic [$bits(mcu_mbox_sram_req_if.resp.rdata.data)-1:0] sram_rdata_cor;
logic invalid_sram_addr;
logic valid_sram_addr;

assign hwif_in.rst_b = rst_b;

///////////////////////////////////////////////
// Valid User 
///////////////////////////////////////////////


//Check if SoC request is coming from a valid user
//There are 5 valid user registers, check if user attribute matches any of them
//Check if user matches Default Valid user parameter - this user value is always valid
//Check if request is coming from MCU (privilaged access)
always_comb begin
    mbox_valid_user = '0;
    for (int i=0; i < 5; i++) begin
        mbox_valid_user |= (cif_resp_if.req_data.user == valid_mbox_users[i]);
    end
    mbox_valid_user |= cif_resp_if.req_data.user == DEF_MBOX_VALID_AXI_USER[cif_resp_if.USER_WIDTH-1:0];
    mbox_valid_user |= mbox_axi_root_user;
end

assign mbox_valid_user_req = mbox_valid_user & cif_resp_if.dv;
assign mbox_valid_user_error = !mbox_valid_user & cif_resp_if.dv;

///////////////////////////////////////////////
// User checks 
///////////////////////////////////////////////

// No need to add in mbox_valid_user_req since to access the CSRs you need to be a valid user
assign mbox_target_user     = hwif_out.mbox_target_user_valid.valid.value & (hwif_out.mbox_target_user.user.value == cif_resp_if.req_data.user);
assign mbox_requester_user  = hwif_out.mbox_user.user.value == cif_resp_if.req_data.user;
assign mbox_axi_root_user   = strap_root_axi_user == cif_resp_if.req_data.user;

assign mbox_target_user_req     = cif_resp_if.dv & mbox_target_user   ; 
assign mbox_requester_user_req  = cif_resp_if.dv & mbox_requester_user;
assign mbox_axi_root_user_req   = cif_resp_if.dv & mbox_axi_root_user ;

///////////////////////////////////////////////
// CSR access checks
///////////////////////////////////////////////


// We want to block all writes if LOCK is 0 or we have started to zero out the SRAM.
assign lock_set = hwif_out.mbox_lock.lock.value & !mbox_sram_zero_in_progress;
assign hwif_in.lock_set = lock_set;
assign valid_requester_target_req = lock_set & (mbox_axi_root_user_req | mbox_requester_user_req | mbox_target_user_req);
assign valid_target_req           = lock_set & (mbox_axi_root_user_req | mbox_target_user_req);
assign valid_requester_req        = lock_set & (mbox_axi_root_user_req | mbox_requester_user_req);
assign valid_root_req             = lock_set & (mbox_axi_root_user_req);

assign hwif_in.valid_requester_target_req = valid_requester_target_req; 
assign hwif_in.valid_target_req           = valid_target_req         ; 
assign hwif_in.valid_requester_req        = valid_requester_req      ; 
assign hwif_in.valid_root_req             = valid_root_req           ; 


///////////////////////////////////////////////
// MBOX Lock and Clearing of Registers
///////////////////////////////////////////////

always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
        execute_prev <= 1'b0;
    end else begin
        execute_prev <= hwif_out.mbox_execute.execute.value;
    end
end

always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
       mbox_sram_zero_done <= 1'b0;
       mbox_sram_zero_in_progress <= 1'b0;
    end else begin
       mbox_sram_zero_done        <= mbox_release; // FIXME - need real logic behind this.
       mbox_sram_zero_in_progress <= mbox_release; // FIXME - need real logic behind this.
    end
end

// Release the mailbox on clock cycle after execute is cleared
assign mbox_release = !hwif_out.mbox_execute.execute.value & execute_prev;  

assign hwif_in.mbox_lock.lock.hwset = !lock_set & hwif_out.mbox_lock.lock.swmod; 

// No need to check if lock_set because mbox_release can't happen unless lock was set.
// MBOX_LOCK isn't cleared until SRAM is zeroed out.
assign hwif_in.mbox_lock.lock.hwclr = mbox_sram_zero_done; 
// All other registers are cleared on MBOX release when execute is cleared.
assign hwif_in.mbox_dlen.length.hwclr = mbox_release; 
assign hwif_in.mbox_cmd_status.status.hwclr = mbox_release; 
assign hwif_in.mbox_target_user_valid.valid.hwclr = mbox_release; 
assign hwif_in.mbox_target_status.status.hwclr = mbox_release; 
assign hwif_in.mbox_target_status.done.hwclr = mbox_release; 
assign hwif_in.mbox_cmd.command.hwclr = mbox_release; 
assign hwif_in.mbox_target_user.user.hwclr = mbox_release; 

// User locking is done via RDL. So only need to pass the user value to the HWIF if
// there is a valid user request.
assign hwif_in.mbox_user.user.next = cif_resp_if.req_data.user & {$bits(cif_resp_if.req_data.user){mbox_valid_user_req}};

///////////////////////////////////////////////
// Status signals 
///////////////////////////////////////////////


//Notify uC when it has the lock and SoC is requesting the lock
assign soc_req_mbox_locked = lock_set && (hwif_out.mbox_user.user.value == strap_root_axi_user) && hwif_out.mbox_lock.lock.swmod && (cif_resp_if.req_data.user != strap_root_axi_user);

assign soc_mbox_data_available = hwif_out.mbox_execute.execute.value && (hwif_out.mbox_user.user.value != strap_root_axi_user);
assign root_mbox_data_available = hwif_out.mbox_execute.execute.value && (hwif_out.mbox_user.user.value == strap_root_axi_user);

assign target_user_done = hwif_out.mbox_target_status.done.value;

///////////////////////////////////////////////
// Memory Interface 
///////////////////////////////////////////////

// RDL size is fixed. So need to detect invalid addresses to the SRAM
assign invalid_sram_addr = (hwif_out.MBOX_SRAM.addr >= MCU_MBOX_SRAM_SIZE_BYTES);
assign valid_sram_addr = !invalid_sram_addr;





/////
// SRAM Controls
/////
// Only send request if the address is valid and proper user access
assign mcu_mbox_sram_req_if.req.addr = {MCU_MBOX_SRAM_ADDR_W{(valid_requester_target_req & valid_sram_addr)}} & hwif_out.MBOX_SRAM.addr[MCU_MBOX_SRAM_ADDR_W-1:0];
assign mcu_mbox_sram_req_if.req.cs   = valid_requester_target_req & valid_sram_addr & hwif_out.MBOX_SRAM.req;
assign mcu_mbox_sram_req_if.req.we   = valid_requester_target_req & valid_sram_addr & hwif_out.MBOX_SRAM.req_is_wr;

/////
// SRAM Write
/////

// Assign same cycle.
assign hwif_in.MBOX_SRAM.wr_ack = hwif_out.MBOX_SRAM.req & hwif_out.MBOX_SRAM.req_is_wr;

// Setting write data only if valid address and prper user access
assign mcu_mbox_sram_req_if.req.wdata.data = {MCU_MBOX_SRAM_DATA_W{(valid_requester_target_req & valid_sram_addr)}} & hwif_out.MBOX_SRAM.wr_data;

// From RISC-V core beh_lib.sv
// 32-bit data width hardcoded
// 7-bit ECC width hardcoded
rvecc_encode mbox_ecc_encode (
    .din    (hwif_out.MBOX_SRAM.wr_data), 
    .ecc_out(mcu_mbox_sram_req_if.req.wdata.ecc)
);

/////
// SRAM Read  
/////
// Enable ECC when data comes back 1 cycle after request and it is a valid SRAM address and valid requester.
always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
        sram_rd_ecc_en <= 1'b0;
    end else begin
        sram_rd_ecc_en <= hwif_out.MBOX_SRAM.req & ~hwif_out.MBOX_SRAM.req_is_wr & valid_sram_addr & valid_requester_target_req;
    end
end

rvecc_decode ecc_decode (
    .en              (sram_rd_ecc_en       ),
    .sed_ded         ( 1'b0                ),    // 1 : means only detection
    .din             (mcu_mbox_sram_req_if.resp.rdata.data),
    .ecc_in          (mcu_mbox_sram_req_if.resp.rdata.ecc       ),
    .dout            (sram_rdata_cor       ),
    .ecc_out         (                     ), // Unused in today's design
    .single_ecc_error(sram_single_ecc_error), // TODO use to flag write-back
    .double_ecc_error(sram_double_ecc_error)  // TODO use to flag command error
);

// Only send data back if the address is valid
assign hwif_in.MBOX_SRAM.rd_data = {MCU_MBOX_SRAM_DATA_W{valid_sram_addr}} & sram_rdata_cor; 

// No AXI error response to avoid NMI errors on ECC error
// Clearing done in RDL generated code
always_comb hwif_in.mbox_hw_status.ecc_single_error.hwset = sram_single_ecc_error;
always_comb hwif_in.mbox_hw_status.ecc_double_error.hwset = sram_double_ecc_error;

// Ack back when data is valid for a read
always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
        mbox_sram_rd_ack <= 1'b0;
    end else begin
        mbox_sram_rd_ack <= hwif_out.MBOX_SRAM.req & ~hwif_out.MBOX_SRAM.req_is_wr;
    end
end
// Delay 1 clock cycle to match data.
assign hwif_in.MBOX_SRAM.rd_ack = mbox_sram_rd_ack; 

///////////////////////////////////////////////
// Error response 
///////////////////////////////////////////////
// Anytime an error is detected we pass it back on the interface.
// All error sources in this module shall only assert when DV is asserted.
// This logic is just an aggregate of the error sources and will not check
// for DV.
assign cif_resp_if.error = mbox_valid_user_error | csr_read_error | csr_write_error; 
                           


///////////////////////////////////////////////
// MBOX CSR                 
///////////////////////////////////////////////
logic [$bits(cif_resp_if.req_data.wdata)-1:0] s_cpuif_wr_biten;
logic s_cpuif_req_stall_wr_nc;
logic s_cpuif_req_stall_rd_nc;
logic s_cpuif_rd_ack_nc;
logic s_cpuif_wr_ack_nc;

genvar i;
generate
    for (i=0;i<32;i++) begin: assign_biten_from_wstrb
        assign s_cpuif_wr_biten[i] = cif_resp_if.req_data.wstrb[i/8];
    end
endgenerate

// Hold interface when SRAM is being read
assign cif_resp_if.hold = hwif_out.MBOX_SRAM.req & ~hwif_out.MBOX_SRAM.req_is_wr; 

mcu_mbox_csr
mcu_mbox_csr(
    .clk(clk),
    .rst('0),

    .s_cpuif_req(mbox_valid_user_req),
    .s_cpuif_req_is_wr(cif_resp_if.req_data.write),
    .s_cpuif_addr(cif_resp_if.req_data.addr[MCU_MBOX_CSR_ADDR_WIDTH-1:0]),
    .s_cpuif_wr_data(cif_resp_if.req_data.wdata),
    .s_cpuif_wr_biten(s_cpuif_wr_biten),
    .s_cpuif_req_stall_wr(s_cpuif_req_stall_wr_nc),
    .s_cpuif_req_stall_rd(s_cpuif_req_stall_rd_nc),
    .s_cpuif_rd_ack(s_cpuif_rd_ack_nc),
    .s_cpuif_rd_err(csr_read_error),
    .s_cpuif_rd_data(cif_resp_if.rdata),
    .s_cpuif_wr_ack(s_cpuif_wr_ack_nc),
    .s_cpuif_wr_err(csr_write_error),

    .hwif_in(hwif_in),
    .hwif_out(hwif_out)
);

// Strobe writes to SRAM are not supported
`CALIPTRA_ASSERT_NEVER(ERR_MCU_MBOX_NO_STRB_TO_SRAM, (hwif_out.MBOX_SRAM.req && hwif_out.MBOX_SRAM.req_is_wr && !(&hwif_out.MBOX_SRAM.wr_biten)), clk, !rst_b)


endmodule
