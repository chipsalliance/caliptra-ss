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

`ifndef VERILATOR

`include "caliptra_ss_includes.svh"

interface fuse_ctrl_cov_if
(
    input logic clk_i,
    input logic rst_ni
);
    import axi_struct_pkg::*;
    import otp_ctrl_reg_pkg::*;
    import otp_ctrl_pkg::*;

    /** fuse_ctrl_filter:
     *
     * Make sure all AXI user IDs are seen for all registers involved
     * in an AXI write request.
     */

    logic [31:0] core_axi_wr_req_awaddr;
    logic [31:0] core_axi_wr_req_awuser;
    assign core_axi_wr_req_awaddr = fuse_ctrl_filter.core_axi_wr_req.awaddr;
    assign core_axi_wr_req_awuser = fuse_ctrl_filter.core_axi_wr_req.awuser;

    covergroup fuse_ctrl_filter_cg @(posedge clk_i);
        option.per_instance = 1;

        fuse_ctrl_filter_awaddr_cp: coverpoint core_axi_wr_req_awaddr
        {
            bins DirectAccessCmd      = { 32'h7000_0060 };
            bins DirectAccessAddress  = { 32'h7000_0064 };
            bins DirectAccessWData0   = { 32'h7000_0068 };
            bins DirectAccessWData1   = { 32'h7000_006c };
        }

        fuse_ctrl_filter_awuser_cp: coverpoint core_axi_wr_req_awuser
        {
            bins CptraSsStrapClptraCoreAxiUser = { CPTRA_SS_STRAP_CLPTRA_CORE_AXI_USER };
            bins CptraSsStrapMcuLsuAxiUser     = { CPTRA_SS_STRAP_MCU_LSU_AXI_USER };
        }

        fuser_ctrl_filter_cr: cross fuse_ctrl_filter_awaddr_cp, fuse_ctrl_filter_awuser_cp;
    endgroup

endinterface

`endif