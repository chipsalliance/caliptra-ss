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
    import otp_ctrl_part_pkg::*;
    import lc_ctrl_state_pkg::*;

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

    /** fuse_ctrl test unlock tokens:
     *
     *  Verify that all test unlock tokens are broadcasted and transitions are correct.
     */

    logic [31:0] test_unlock_token_idx;
    assign test_unlock_token_idx = `FC_PATH.test_unlock_token_idx;

    lc_token_t test_unlock_token;
    lc_token_t test_exit_dev_token;
    lc_token_t dev_exit_prod_token;
    lc_token_t prod_exit_prodend_token;
    assign test_unlock_token       = `FC_PATH.otp_lc_data_o.test_unlock_token;
    assign test_exit_dev_token     = `FC_PATH.otp_lc_data_o.test_exit_dev_token;
    assign dev_exit_prod_token     = `FC_PATH.otp_lc_data_o.dev_exit_prod_token;
    assign prod_exit_prodend_token = `FC_PATH.otp_lc_data_o.prod_exit_prodend_token;

    covergroup fuse_ctrl_test_unlock_tokens_cg @(posedge clk_i);
        option.per_instance = 1;

        fuse_ctrl_test_unlock_token_idx_cp: coverpoint test_unlock_token_idx
        {
            bins CptraSsTestUnlockTokenOffsets[] = {
                CptraSsTestUnlockToken0Offset,
                CptraSsTestUnlockToken1Offset,
                CptraSsTestUnlockToken2Offset,
                CptraSsTestUnlockToken3Offset,
                CptraSsTestUnlockToken4Offset,
                CptraSsTestUnlockToken5Offset,
                CptraSsTestUnlockToken6Offset,
                '0
            };
        }

        fuse_ctrl_test_unlock_token_transitions_cp: coverpoint test_unlock_token_idx
        {
            bins CptraSsTestUnlockToken0Transitions = ( 
                CptraSsTestUnlockToken0Offset => '0 => CptraSsTestUnlockToken1Offset,
                CptraSsTestUnlockToken0Offset => '0 => CptraSsTestUnlockToken2Offset,
                CptraSsTestUnlockToken0Offset => '0 => CptraSsTestUnlockToken3Offset,
                CptraSsTestUnlockToken0Offset => '0 => CptraSsTestUnlockToken4Offset,
                CptraSsTestUnlockToken0Offset => '0 => CptraSsTestUnlockToken5Offset,
                CptraSsTestUnlockToken0Offset => '0 => CptraSsTestUnlockToken6Offset
            );
            bins CptraSsTestUnlockToken1Transitions = (
                CptraSsTestUnlockToken1Offset => '0 => CptraSsTestUnlockToken2Offset,
                CptraSsTestUnlockToken1Offset => '0 => CptraSsTestUnlockToken3Offset,
                CptraSsTestUnlockToken1Offset => '0 => CptraSsTestUnlockToken4Offset,
                CptraSsTestUnlockToken1Offset => '0 => CptraSsTestUnlockToken5Offset,
                CptraSsTestUnlockToken1Offset => '0 => CptraSsTestUnlockToken6Offset
            );
            bins CptraSsTestUnlockToken2Transitions = ( 
                CptraSsTestUnlockToken2Offset => '0 => CptraSsTestUnlockToken3Offset,
                CptraSsTestUnlockToken2Offset => '0 => CptraSsTestUnlockToken4Offset,
                CptraSsTestUnlockToken2Offset => '0 => CptraSsTestUnlockToken5Offset,
                CptraSsTestUnlockToken2Offset => '0 => CptraSsTestUnlockToken6Offset
            );
            bins CptraSsTestUnlockToken3Transitions = ( 
                CptraSsTestUnlockToken3Offset => '0 => CptraSsTestUnlockToken4Offset,
                CptraSsTestUnlockToken3Offset => '0 => CptraSsTestUnlockToken5Offset,
                CptraSsTestUnlockToken3Offset => '0 => CptraSsTestUnlockToken6Offset
            );
            bins CptraSsTestUnlockToken4Transitions = ( 
                CptraSsTestUnlockToken4Offset => '0 => CptraSsTestUnlockToken5Offset,
                CptraSsTestUnlockToken4Offset => '0 => CptraSsTestUnlockToken6Offset
            );
            bins CptraSsTestUnlockToken5Transitions = ( 
                CptraSsTestUnlockToken5Offset => '0 => CptraSsTestUnlockToken6Offset
            );

            illegal_bins CptraSsTestUnlockToken1IllegalTransitions = (
                CptraSsTestUnlockToken1Offset => '0 => CptraSsTestUnlockToken0Offset
            );

            illegal_bins CptraSsTestUnlockToken2IllegalTransitions = (
                CptraSsTestUnlockToken2Offset => '0 => CptraSsTestUnlockToken0Offset,
                CptraSsTestUnlockToken2Offset => '0 => CptraSsTestUnlockToken1Offset
            );

            illegal_bins CptraSsTestUnlockToken3IllegalTransitions = (
                CptraSsTestUnlockToken3Offset => '0 => CptraSsTestUnlockToken0Offset,
                CptraSsTestUnlockToken3Offset => '0 => CptraSsTestUnlockToken1Offset,
                CptraSsTestUnlockToken3Offset => '0 => CptraSsTestUnlockToken2Offset
            );

            illegal_bins CptraSsTestUnlockToken4IllegalTransitions = (
                CptraSsTestUnlockToken4Offset => '0 => CptraSsTestUnlockToken0Offset,
                CptraSsTestUnlockToken4Offset => '0 => CptraSsTestUnlockToken1Offset,
                CptraSsTestUnlockToken4Offset => '0 => CptraSsTestUnlockToken2Offset,
                CptraSsTestUnlockToken4Offset => '0 => CptraSsTestUnlockToken3Offset
            );

            illegal_bins CptraSsTestUnlockToken5IllegalTransitions = (
                CptraSsTestUnlockToken5Offset => '0 => CptraSsTestUnlockToken0Offset,
                CptraSsTestUnlockToken5Offset => '0 => CptraSsTestUnlockToken1Offset,
                CptraSsTestUnlockToken5Offset => '0 => CptraSsTestUnlockToken2Offset,
                CptraSsTestUnlockToken5Offset => '0 => CptraSsTestUnlockToken3Offset,
                CptraSsTestUnlockToken5Offset => '0 => CptraSsTestUnlockToken4Offset
            );

            illegal_bins CptraSsTestUnlockToken6IllegalTransitions = (
                CptraSsTestUnlockToken6Offset => '0 => CptraSsTestUnlockToken0Offset,
                CptraSsTestUnlockToken6Offset => '0 => CptraSsTestUnlockToken1Offset,
                CptraSsTestUnlockToken6Offset => '0 => CptraSsTestUnlockToken2Offset,
                CptraSsTestUnlockToken6Offset => '0 => CptraSsTestUnlockToken3Offset,
                CptraSsTestUnlockToken6Offset => '0 => CptraSsTestUnlockToken4Offset,
                CptraSsTestUnlockToken6Offset => '0 => CptraSsTestUnlockToken5Offset
            );           
        }

        fuse_ctrl_test_unlock_token_cp: coverpoint test_unlock_token
        {
            bins TestUnlockToken = { [1:] };
        }
        fuse_ctrl_test_exit_dev_token_cp: coverpoint test_exit_dev_token
        {
            bins TestExitDevToken = { [1:] };
        }
        fuse_ctrl_dev_exit_prod_token_cp: coverpoint dev_exit_prod_token
        {
            bins DevExitProdToken = { [1:] };
        }
        fuse_ctrl_prod_exit_prodend_token_cp: coverpoint prod_exit_prodend_token
        {
            bins ProdExitProdendToken = { [1:] };
        }

    endgroup

    /** fuse_ctrl public-key hash volatile lock:
     *
     *  All possible locking indices should be covered.
     */

    if (NumVendorPkFuses > 1) begin

        logic [31:0] pk_hash_volatile_lock;
        assign pk_hash_volatile_lock = `FC_PATH.reg2hw.vendor_pk_hash_volatile_lock; 

        covergroup fuse_ctrl_pk_hash_volatile_lock_cg @(posedge clk_i);
            option.per_instance = 1;

            fuse_ctrl_pk_hash_volatile_lock_cp: coverpoint pk_hash_volatile_lock
            {
                bins PkHashVolatileLock[] = { [0:NumVendorPkFuses-1] };
            }
        endgroup

    end

endinterface

`endif