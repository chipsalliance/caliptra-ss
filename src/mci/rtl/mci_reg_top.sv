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

    // WDT specific signals
    output logic wdt_timer1_timeout_serviced,
    output logic wdt_timer2_timeout_serviced,
    input  logic t1_timeout_p,
    input  logic t2_timeout_p,

    // MCU SRAM specific signals
    input logic mcu_sram_single_ecc_error,
    input logic mcu_sram_double_ecc_error,


    
    // Caliptra internal fabric response interface
    cif_if.response  cif_resp_if

    );

// Error signals
logic mci_reg_read_error;
logic mci_reg_write_error;

// REG HWIF signals
mci_reg__in_t   mci_reg_hwif_in;


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
assign mci_reg_hwif_in.cptra_req    = '0;     // FIXME
assign mci_reg_hwif_in.mcu_req      = '0;      // FIXME
assign mci_reg_hwif_in.soc_req = '0; // FIXME


assign mci_reg_hwif_in.CAPABILITIES = '0; // FIXME
assign mci_reg_hwif_in.HW_REV_ID = '0; // FIXME
assign mci_reg_hwif_in.HW_CONFIG = '0; // FIXME
assign mci_reg_hwif_in.FLOW_STATUS = '0; // FIXME
assign mci_reg_hwif_in.RESET_REASON = '0; // FIXME
assign mci_reg_hwif_in.HW_ERROR_FATAL = '0; // FIXME
assign mci_reg_hwif_in.HW_ERROR_NON_FATAL = '0; // FIXME
assign mci_reg_hwif_in.FW_ERROR_FATAL = '0; // FIXME
assign mci_reg_hwif_in.FW_ERROR_NON_FATAL = '0; // FIXME
assign mci_reg_hwif_in.WDT_STATUS = '0; // FIXME
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


// WDT timeout Serviced
// NOTE: Since error_internal_intr_r is Write-1-to-clear, capture writes to the
//       WDT interrupt bits to detect the interrupt being serviced.
//       It would be preferable to decode this from interrupt signals somehow,
//       but that would require modifying interrupt register RDL which has been
//       standardized.
always_ff @(posedge clk or negedge mci_rst_b) begin
    if(!mci_rst_b) begin
        wdt_timer1_timeout_serviced <= 1'b0;
        wdt_timer2_timeout_serviced <= 1'b0;
    end
    else if (cif_resp_if.dv && cif_resp_if.req_data.write && (cif_resp_if.req_data.addr[MCI_REG_MIN_ADDR_WIDTH-1:0] == MCI_REG_ADDR_WIDTH'(`MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R))) begin // FIXME should I be using a more global define than the MCI_REG_INTR?
        wdt_timer1_timeout_serviced <= cif_resp_if.req_data.wdata[`MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_LOW];
        wdt_timer2_timeout_serviced <= cif_resp_if.req_data.wdata[`MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_LOW];
    end
    else begin
        wdt_timer1_timeout_serviced <= 1'b0;
        wdt_timer2_timeout_serviced <= 1'b0;
    end
end


// WDT timeout Interrupts
assign mci_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_wdt_timer1_timeout_sts.hwset = t1_timeout_p;
assign mci_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_wdt_timer2_timeout_sts.hwset = t2_timeout_p;


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
