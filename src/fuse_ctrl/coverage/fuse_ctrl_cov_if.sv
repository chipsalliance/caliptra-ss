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
`include "caliptra_ss_top_tb_path_defines.svh"

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

    /** fuse_ctrl fuses:
     *
     * Verify that all fuses are provisioned alongside their digest fields if available.
     */

    logic [21:0] fc_mem [0:2047];
    assign fc_mem = `CPTRA_SS_TB_TOP_NAME.u_otp.u_prim_ram_1p_adv.u_mem.mem;

    `define FUSE_CG(ADDR, SIZE)                                                             \
      covergroup fuse_``ADDR``_cg @(posedge clk_i);                                         \
        option.per_instance = 1;                                                            \
        fuse_``ADDR``_cp: coverpoint ((16+6)*(SIZE/2))'(fc_mem[(ADDR/2):((ADDR+SIZE)/2)-1]) \
        {                                                                                   \
            bins Fuse = { [1:] };                                                           \
        }                                                                                   \
      endgroup

    // SECRET_TEST_UNLOCK_PARTITION
    `FUSE_CG(CptraCoreManufDebugUnlockTokenOffset, CptraCoreManufDebugUnlockTokenSize)
    `FUSE_CG(SecretTestUnlockPartitionDigestOffset, SecretTestUnlockPartitionDigestSize)
    // SECRET_MANUF_PARTITION
    `FUSE_CG(CptraCoreUdsSeedOffset, CptraCoreUdsSeedSize)
    `FUSE_CG(SecretManufPartitionDigestOffset, SecretManufPartitionDigestSize)
    // SECRET_PROD_PARTITION_0
    `FUSE_CG(CptraCoreFieldEntropy0Offset, CptraCoreFieldEntropy0Size)
    `FUSE_CG(SecretProdPartition0DigestOffset, SecretProdPartition0DigestSize)
    // TODO: fill all fuses

endinterface

`endif