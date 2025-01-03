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

// Reads and writes occure in 1 clock cycles
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
        .s_cpuif_req_stall_rd   ('0),   // FIXME why isn't this connected?
        .s_cpuif_rd_ack         (),     // FIXME why isn't this used?
        .s_cpuif_rd_err         (mci_reg_read_error),
        .s_cpuif_rd_data        (cif_resp_if.rdata),   // FIXME should this be masked for security?
        .s_cpuif_wr_ack         (),     // FIXME why isn't this used?
        .s_cpuif_wr_err         (mci_reg_write_error),

        .hwif_in                (mci_reg_hwif_in),
        .hwif_out               (mci_reg_hwif_out)

);


endmodule
