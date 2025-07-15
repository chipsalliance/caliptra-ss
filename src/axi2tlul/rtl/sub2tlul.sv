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

// -------------------------------------------------------------
// AXI TLUL Write Shim
// -------------------------------------------------------------
// Description:
//   Shim to convert AXI protocol writes into TLUL
//
// Limitations:
//   - When multiple ID tracking is enabled, write responses are returned in the
//     same order they are received, regardless of ID.
//
// -------------------------------------------------------------

module sub2tlul 
    import axi_pkg::*;
    import tlul_pkg::*;
    #(
        parameter AW = 32,         // Address Width
        parameter DW = 32,         // Data Width
                  BC = DW/8,       // Byte Count
                  BW = $clog2(BC), // Byte count Width
        parameter UW = 32,         // User Width
        parameter IW = 1,          // ID Width
                  ID_NUM = 1 << IW, // Don't override

        parameter EX_EN = 0,   // Enable exclusive access tracking w/ AxLOCK
        parameter C_LAT = 0    // Component latency in clock cycles from (dv&&!hld) -> rdata
                            // Must be const per component
                            // For registers, typically 0
                            // For SRAM, 1 or more
    ) (
        input clk,
        input rst_n,

        //COMPONENT INF
        input   logic          dv,
        input   logic [AW-1:0] addr, // Byte address
        input   logic          write,
        input   logic [UW-1:0] user,
        input   logic [IW-1:0] id,
        input   logic [DW-1:0] wdata, // Requires: Component dwidth == AXI dwidth
        input   logic [BC-1:0] wstrb, // Requires: Component dwidth == AXI dwidth
        input   logic [2:0]    size, 
        output  logic [DW-1:0] rdata, // Requires: Component dwidth == AXI dwidth
        input   logic          last, // Asserted with final 'dv' of a burst
        output  logic          hld,
        output  logic          rd_err,
        output  logic          wr_err,

        //TLUL INF
        output  tlul_pkg::tl_h2d_t tl_o,
        input   tlul_pkg::tl_d2h_t tl_i
    );

    // Setting instruction type to False as all accesses to OTP are data accesses
    localparam caliptra_prim_mubi_pkg::mubi4_t  instr_type = caliptra_prim_mubi_pkg::MuBi4False;

    // AXI SUB TO TL-UL REQUEST
    logic       pending_txn;
    tl_a_op_e   opcode;
    logic [3:0] mask_local;
    logic [TL_DW-1:0] a_data_local;

    typedef enum logic [1:0] { 
        no_txn = 2'b00, 
        valid_get_txn = 2'b01, 
        valid_put_txn = 2'b10 
    } txn_state_e;

    txn_state_e cur_txn;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            cur_txn <= no_txn;
        end
        else if (opcode == Get && tl_o.a_valid) begin
            cur_txn <= valid_get_txn;
        end
        else if ((opcode == PutFullData || opcode == PutPartialData) && tl_o.a_valid) begin
            cur_txn <= valid_put_txn;
        end
        else if (cur_txn == valid_get_txn && tl_i.d_opcode == AccessAckData && tl_i.d_valid) begin
            cur_txn <= no_txn;
        end
        else if (cur_txn == valid_put_txn && tl_i.d_opcode == AccessAck && tl_i.d_valid) begin
            cur_txn <= no_txn;
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            pending_txn         <= 0;
        end
        else if (dv && tl_i.a_ready && ~tl_i.d_valid) begin   
            pending_txn         <= 1;
        end
        else if (dv && tl_i.d_valid) begin
            pending_txn         <= 0;
        end
    end

    assign opcode = !write ? Get : ((wstrb == '1) ? PutFullData : PutPartialData);
    assign mask_local   = !write ? user[21:18] : wstrb;
    assign a_data_local = !write ? TL_DW'(0)   : wdata;

    assign tl_o.a_address   = addr;
    assign tl_o.a_valid     = dv &  ~pending_txn;
    assign tl_o.a_opcode    = opcode;
    assign tl_o.a_source    = id;
    assign tl_o.a_mask      = mask_local;
    assign tl_o.a_data      = a_data_local;
    assign tl_o.a_size      = size[top_pkg::TL_SZW-1:0];

    // TL-UL TO AXI SUB RESPONSE
    assign rdata        = (dv && tl_i.d_valid && (tl_i.d_source == id)) ? tl_i.d_data : 0;
    assign hld          = dv & tl_o.a_valid & (~tl_i.a_ready | ~tl_i.d_valid) | 
                            ((cur_txn == valid_get_txn) & ((tl_i.d_opcode != AccessAckData) | ((tl_i.d_opcode == AccessAckData) & ~tl_i.d_valid)) );
    assign tl_o.d_ready = tl_i.d_valid; 
    assign rd_err       = ~write &  tl_i.d_error & tl_i.d_valid;
    assign wr_err       = write &  tl_i.d_error & tl_i.d_valid;

    //TLUL unused signals: a_param, d_param, d_sink, d_size   (dropped)
    assign tl_o.a_param = 3'h0;

    logic [H2DCmdIntgWidth-1:0]    cmd_intg;
    logic [DataIntgWidth-1:0]      data_intg;

    axi2tlul_cmd_intg_gen #( 
        .EnableDataIntgGen  (1),
        .AW (AW)
    ) u_axi2tlul_cmd_intg_gen (
        .instr_type_i   (instr_type),
        .addr_i         (addr),
        .opcode_i       (opcode),
        .mask_i         (mask_local),
        .data_i         (a_data_local),
        .cmd_intg       (cmd_intg),
        .data_intg      (data_intg) 
    );

    assign tl_o.a_user = {  5'b0,
                            instr_type, 
                            cmd_intg,
                            data_intg };

endmodule
