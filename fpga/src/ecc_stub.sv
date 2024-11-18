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
//======================================================================
//
// ecc_top.sv
// --------
// top-level wrapper for ecc architecture including:
// 1- ecc_dsa_ctrl module as ecc engin
// 2- ecc_reg module as register memory of ecc to interface with external
// 3- ahb_slv_sif module to handle AHB-lite interface
//======================================================================

module ecc_top
    import kv_defines_pkg::*;
    #(
    parameter AHB_ADDR_WIDTH = 32,
    parameter AHB_DATA_WIDTH = 32,
    parameter CLIENT_DATA_WIDTH = 32
    )
    (
    input wire                        clk,
    input wire                        reset_n,
    input wire                        cptra_pwrgood,

    //AHB Lite Interface
    input wire  [AHB_ADDR_WIDTH-1:0]  haddr_i,
    input wire  [AHB_DATA_WIDTH-1:0]  hwdata_i,
    input wire                        hsel_i,
    input wire                        hwrite_i,
    input wire                        hready_i,
    input wire  [1:0]                 htrans_i,
    input wire  [2:0]                 hsize_i,

    output logic                      hresp_o,
    output logic                      hreadyout_o,
    output logic [AHB_DATA_WIDTH-1:0] hrdata_o,

    // KV interface
    output kv_read_t [1:0] kv_read,
    output kv_write_t kv_write,
    input kv_rd_resp_t [1:0] kv_rd_resp,
    input kv_wr_resp_t kv_wr_resp,   
    //PCR Signing
    input pcr_signing_t pcr_signing_data,

    output logic busy_o,

    output logic error_intr,
    output logic notif_intr,
    input  logic debugUnlock_or_scan_mode_switch
);
// Drive zero on output signals
assign hresp_o = 0;
assign hreadyout_o = 0;
assign hrdata_o = 0;
assign kv_read = 0;
assign kv_write = 0;
assign busy_o = 0;
assign error_intr = 0;
assign notif_intr = 0;

endmodule
