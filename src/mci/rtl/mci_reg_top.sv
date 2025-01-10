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

`include "mci_reg_defines.svh"

module mci_reg_top 
    import mci_reg_pkg::*;
    #(
    )
    (
    input logic clk,

    // MCI Resets
    input logic mci_rst_b,
    input logic mci_pwrgood,

    // REG HWIF signals
    output mci_reg__out_t mci_reg_hwif_out,

    // AXI Privileged requests
    input logic clp_req,
    input logic mcu_req,

    // WDT specific signals
    output logic wdt_timer1_timeout_serviced,
    output logic wdt_timer2_timeout_serviced,
    input  logic t1_timeout,
    input  logic t2_timeout,
    input  logic t1_timeout_p,
    input  logic t2_timeout_p,
    
    // SOC Interrupts
    output logic error_fatal,

    // input NMI
    input logic nmi_intr,

    // MCU SRAM specific signals
    input logic mcu_sram_single_ecc_error,
    input logic mcu_sram_double_ecc_error,


    
    // Caliptra internal fabric response interface
    cif_if.response  cif_resp_if

    );

// Error signals
logic mci_reg_read_error;
logic mci_reg_write_error;
logic unmasked_hw_error_fatal_write;

// REG HWIF signals
mci_reg__in_t   mci_reg_hwif_in;

// WDT signals
logic   error_wdt_timer1_timeout_sts_prev;
logic   error_wdt_timer2_timeout_sts_prev;

// Byte Enable mapping
logic [MCI_REG_DATA_WIDTH-1:0] c_cpuif_wr_biten;

///////////////////////////////////////////////
// Map CIF WSTRB to BITEN of CSR block
///////////////////////////////////////////////
genvar i;
generate 
    for (i = 0; i < MCI_REG_DATA_WIDTH; i = i + 1) begin : map_wstrb_to_biten
        assign c_cpuif_wr_biten[i] = cif_resp_if.req_data.wstrb[i/8];
    end
endgenerate


///////////////////////////////////////////////
// Error handling logic
///////////////////////////////////////////////

assign cif_resp_if.error = mci_reg_read_error | mci_reg_write_error;

///////////////////////////////////////////////
// Hold response logic
///////////////////////////////////////////////

// Reads and writes occur in 1 clock cycles
assign cif_resp_if.hold = '0;


///////////////////////////////////////////////
// Hold response logic
///////////////////////////////////////////////

// Resets
assign mci_reg_hwif_in.mci_rst_b = mci_rst_b;
assign mci_reg_hwif_in.mcu_rst_b = '0; // FIXME
assign mci_reg_hwif_in.mci_pwrgood = mci_pwrgood;

// Agent requests
assign mci_reg_hwif_in.cptra_req    = clp_req;
assign mci_reg_hwif_in.mcu_req      = mcu_req;


assign mci_reg_hwif_in.CAPABILITIES = '0; // FIXME
assign mci_reg_hwif_in.HW_REV_ID = '0; // FIXME
assign mci_reg_hwif_in.HW_CONFIG = '0; // FIXME
assign mci_reg_hwif_in.FLOW_STATUS = '0; // FIXME
assign mci_reg_hwif_in.RESET_REASON = '0; // FIXME
assign mci_reg_hwif_in.HW_ERROR_NON_FATAL = '0; // FIXME
assign mci_reg_hwif_in.MCU_RV_MTIME_L = '0; // FIXME
assign mci_reg_hwif_in.MCU_RV_MTIME_H = '0; // FIXME
assign mci_reg_hwif_in.RESET_REQUEST = '0; // FIXME
assign mci_reg_hwif_in.RESET_ACK = '0; // FIXME
assign mci_reg_hwif_in.CALIPTRA_AXI_ID = '0; // FIXME
assign mci_reg_hwif_in.FW_SRAM_EXEC_REGION_SIZE = '0; // FIXME
assign mci_reg_hwif_in.GENERIC_INPUT_WIRES = '0; // FIXME
assign mci_reg_hwif_in.FUSE_WR_DONE = '0; // FIXME
assign mci_reg_hwif_in.PROD_DEBUG_UNLOCK_PK_HASH_REG = '0; // FIXME
assign mci_reg_hwif_in.STICKY_DATA_VAULT_CTRL = '0; // FIXME
assign mci_reg_hwif_in.STICKY_DATA_VAULT_ENTRY = '0; // FIXME
assign mci_reg_hwif_in.DATA_VAULT_CTRL = '0; // FIXME
assign mci_reg_hwif_in.DATA_VAULT_ENTRY = '0; // FIXME
assign mci_reg_hwif_in.STICKY_LOCKABLE_SCRATCH_REG_CTRL = '0; // FIXME
assign mci_reg_hwif_in.STICKY_LOCKABLE_SCRATCH_REG = '0; // FIXME
assign mci_reg_hwif_in.LOCKABLE_SCRATCH_REG_CTRL = '0; // FIXME
assign mci_reg_hwif_in.LOCKABLE_SCRATCH_REG = '0; // FIXME


////////////////////////////////////////////////////////
// Write-enables for CPTRA_HW_ERROR_FATAL and CPTRA_HW_ERROR_NON_FATAL
// Also calculate whether or not an unmasked event is being set, so we can
// trigger the SOC interrupt signal
always_comb mci_reg_hwif_in.HW_ERROR_FATAL.mcu_sram_ecc_unc.we  = mcu_sram_double_ecc_error; // FIXME do we need to add a reset window disable like in caliptra?
always_comb mci_reg_hwif_in.HW_ERROR_FATAL.nmi_pin     .we      = nmi_intr;
// Using we+next instead of hwset allows us to encode the reserved fields in some fashion
// other than bit-hot in the future, if needed (e.g. we need to encode > 32 FATAL events)
always_comb mci_reg_hwif_in.HW_ERROR_FATAL.mcu_sram_ecc_unc.next    = 1'b1;
always_comb mci_reg_hwif_in.HW_ERROR_FATAL.nmi_pin     .next        = 1'b1;
// Flag the write even if the field being written to is already set to 1 - this is a new occurrence of the error and should trigger a new interrupt
always_comb unmasked_hw_error_fatal_write = (mci_reg_hwif_in.HW_ERROR_FATAL.nmi_pin     .we      && |mci_reg_hwif_in.HW_ERROR_FATAL.nmi_pin     .next) ||
                                            (mci_reg_hwif_in.HW_ERROR_FATAL.mcu_sram_ecc_unc.we  && |mci_reg_hwif_in.HW_ERROR_FATAL.mcu_sram_ecc_unc.next);


// Interrupt output is set, for any enabled conditions, when a new write
// sets FW_ERROR_FATAL or when a HW condition occurs that sets a bit
// in HW_ERROR_FATAL
// Interrupt only deasserts on reset
always_ff@(posedge clk or negedge mci_rst_b) begin
    if(~mci_rst_b) begin
        error_fatal <= 1'b0;
    end
    // FW write that SETS a new (non-masked) bit results in interrupt assertion
    else if (cif_resp_if.dv &&
             mci_reg_hwif_out.FW_ERROR_FATAL.error_code.swmod &&
             |(cif_resp_if.req_data.wdata & ~mci_reg_hwif_out.FW_ERROR_FATAL.error_code.value)) begin // FIXME do I need to add FW mask like soc_ifc?
        error_fatal <= 1'b1;
    end
    // HW event that SETS a new (non-masked) bit results in interrupt assertion
    else if (unmasked_hw_error_fatal_write) begin
        error_fatal <= 1'b1;
    end
    // NOTE: There is no mechanism to clear interrupt assertion by design.
    //       Platform MUST perform mci_rst_b in order to clear error_fatal
    //       output signal, per the integration spec.
    else begin
        error_fatal <= error_fatal;
    end
end


//TIE-OFFS
always_comb begin
    mci_reg_hwif_in.FW_ERROR_FATAL.error_code.we = 'b0;
    mci_reg_hwif_in.FW_ERROR_FATAL.error_code.next = 'h0;
    mci_reg_hwif_in.FW_ERROR_NON_FATAL.error_code.we = 'b0;
    mci_reg_hwif_in.FW_ERROR_NON_FATAL.error_code.next = 'h0;
end

////////////////////////////////////////////////////////
// WDT
////////////////////////////////////////////////////////
 
//  Looking for negedge on the wdt_timer*-timeout_sts register
//  meaning the interrupt has been serviced by SW. We then 
//  propagate this to the WDT to clear it's status
always_ff @(posedge clk or negedge mci_rst_b) begin
    if(!mci_rst_b) begin
        error_wdt_timer1_timeout_sts_prev <= 1'b0;
        error_wdt_timer2_timeout_sts_prev <= 1'b0;
    end
    else begin
        error_wdt_timer1_timeout_sts_prev <= mci_reg_hwif_out.intr_block_rf.error_internal_intr_r.error_wdt_timer1_timeout_sts.value;
        error_wdt_timer2_timeout_sts_prev <= mci_reg_hwif_out.intr_block_rf.error_internal_intr_r.error_wdt_timer2_timeout_sts.value;
    end
end

assign wdt_timer1_timeout_serviced = error_wdt_timer1_timeout_sts_prev & ~mci_reg_hwif_out.intr_block_rf.error_internal_intr_r.error_wdt_timer1_timeout_sts.value;
assign wdt_timer2_timeout_serviced = error_wdt_timer2_timeout_sts_prev & ~mci_reg_hwif_out.intr_block_rf.error_internal_intr_r.error_wdt_timer2_timeout_sts.value;;


// WDT timeout Interrupts
assign mci_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_wdt_timer1_timeout_sts.hwset = t1_timeout_p;
assign mci_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_wdt_timer2_timeout_sts.hwset = t2_timeout_p;

//Set WDT status reg
always_comb begin
    mci_reg_hwif_in.WDT_STATUS.t1_timeout.next = t1_timeout;
    mci_reg_hwif_in.WDT_STATUS.t2_timeout.next = t2_timeout;
end


// MCU SRAM Interrupts
assign mci_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_mcu_sram_ecc_cor_sts.hwset = mcu_sram_single_ecc_error;

///////////////////////////////////////////////
// MCI REG Module      
///////////////////////////////////////////////
mci_reg i_mci_reg (

        .clk  (clk),
        .rst  ('0), // FIXME why is this tied off in soc_ifc?

        .s_cpuif_req            (cif_resp_if.dv),
        .s_cpuif_req_is_wr      (cif_resp_if.req_data.write),
        .s_cpuif_addr           (cif_resp_if.req_data.addr[MCI_REG_MIN_ADDR_WIDTH-1:0]),
        .s_cpuif_wr_data        (cif_resp_if.req_data.wdata),
        .s_cpuif_wr_biten       (c_cpuif_wr_biten),
        .s_cpuif_req_stall_wr   (),     // FIXME why isn't this used?
        .s_cpuif_req_stall_rd   (),   // FIXME why isn't this connected?
        .s_cpuif_rd_ack         (),     // FIXME why isn't this used?
        .s_cpuif_rd_err         (mci_reg_read_error),
        .s_cpuif_rd_data        (cif_resp_if.rdata),   // FIXME should this be masked for security?
        .s_cpuif_wr_ack         (),     // FIXME why isn't this used?
        .s_cpuif_wr_err         (mci_reg_write_error),

        .hwif_in                (mci_reg_hwif_in),
        .hwif_out               (mci_reg_hwif_out)

);


endmodule
