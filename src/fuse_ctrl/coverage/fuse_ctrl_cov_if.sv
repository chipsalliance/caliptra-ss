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
    import tlul_pkg::*;
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
            bins CptraSsStrapClptraCoreAxiUser = { `CPTRA_SS_TB_TOP_NAME.cptra_ss_strap_caliptra_dma_axi_user_i };
            bins CptraSsStrapMcuLsuAxiUser     = { `CPTRA_SS_TB_TOP_NAME.cptra_ss_strap_mcu_lsu_axi_user_i };
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
      endgroup                                             \
      initial begin                                         \
        fuse_``ADDR``_cg cg_``ADDR``_1 = new();         \       
      end                                           

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
    generate
        logic [31:0] pk_hash_volatile_lock;
        assign pk_hash_volatile_lock = `FC_PATH.reg2hw.vendor_pk_hash_volatile_lock; 
        if (NumVendorPkFuses > 1) begin : gen_pk_hash_cg
          covergroup fuse_ctrl_pk_hash_volatile_lock_cg @(posedge clk_i);
            option.per_instance = 1;
            fuse_ctrl_pk_hash_volatile_lock_cp: coverpoint pk_hash_volatile_lock {
              bins PkHashVolatileLock[] = {[0:NumVendorPkFuses-1]};
            }
          endgroup
      
          fuse_ctrl_pk_hash_volatile_lock_cg cg_inst;  // Declare only!
        end
    endgenerate
      
      initial begin
        // Instantiate the covergroup outside the generate block
        if (NumVendorPkFuses > 1) begin
          gen_pk_hash_cg.cg_inst = new();
        end
      end
      


    /** fuse_ctrl register accesses:
     *
     *  All CSRs need to be exercised.
     */

    tl_h2d_t core_tl_i;
    assign core_tl_i = `FC_PATH.core_tl_i;

    covergroup fuse_ctrl_core_tl_i_cg @(posedge clk_i);
        option.per_instance = 1;

        fuse_ctrl_core_tl_i_read_cp: coverpoint core_tl_i.a_address[12:0] iff (core_tl_i.a_valid && core_tl_i.a_opcode == Get)
        {
            bins ReadableRegisters[] = {
                OTP_CTRL_INTR_STATE_OFFSET, OTP_CTRL_INTR_ENABLE_OFFSET, OTP_CTRL_STATUS_OFFSET, OTP_CTRL_ERR_CODE_0_OFFSET,
                OTP_CTRL_ERR_CODE_1_OFFSET, OTP_CTRL_ERR_CODE_2_OFFSET, OTP_CTRL_ERR_CODE_3_OFFSET, OTP_CTRL_ERR_CODE_4_OFFSET,
                OTP_CTRL_ERR_CODE_5_OFFSET, OTP_CTRL_ERR_CODE_6_OFFSET, OTP_CTRL_ERR_CODE_7_OFFSET, OTP_CTRL_ERR_CODE_8_OFFSET,
                OTP_CTRL_ERR_CODE_9_OFFSET, OTP_CTRL_ERR_CODE_10_OFFSET, OTP_CTRL_ERR_CODE_11_OFFSET, OTP_CTRL_ERR_CODE_12_OFFSET,
                OTP_CTRL_ERR_CODE_13_OFFSET, OTP_CTRL_ERR_CODE_14_OFFSET, OTP_CTRL_ERR_CODE_15_OFFSET, OTP_CTRL_ERR_CODE_16_OFFSET,
                OTP_CTRL_ERR_CODE_17_OFFSET, OTP_CTRL_DIRECT_ACCESS_REGWEN_OFFSET, OTP_CTRL_DIRECT_ACCESS_CMD_OFFSET, OTP_CTRL_DIRECT_ACCESS_ADDRESS_OFFSET,
                OTP_CTRL_DIRECT_ACCESS_WDATA_0_OFFSET, OTP_CTRL_DIRECT_ACCESS_WDATA_1_OFFSET, OTP_CTRL_DIRECT_ACCESS_RDATA_0_OFFSET, OTP_CTRL_DIRECT_ACCESS_RDATA_1_OFFSET,
                OTP_CTRL_CHECK_TRIGGER_REGWEN_OFFSET, OTP_CTRL_CHECK_TRIGGER_OFFSET, OTP_CTRL_CHECK_REGWEN_OFFSET, OTP_CTRL_CHECK_TIMEOUT_OFFSET,
                OTP_CTRL_INTEGRITY_CHECK_PERIOD_OFFSET, OTP_CTRL_CONSISTENCY_CHECK_PERIOD_OFFSET, OTP_CTRL_SW_MANUF_PARTITION_READ_LOCK_OFFSET,
                OTP_CTRL_SVN_PARTITION_READ_LOCK_OFFSET, OTP_CTRL_VENDOR_TEST_PARTITION_READ_LOCK_OFFSET, OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_READ_LOCK_OFFSET,
                OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_READ_LOCK_OFFSET, OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK_OFFSET,
                OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_READ_LOCK_OFFSET, OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK_OFFSET,
                OTP_CTRL_SECRET_TEST_UNLOCK_PARTITION_DIGEST_0_OFFSET, OTP_CTRL_SECRET_TEST_UNLOCK_PARTITION_DIGEST_1_OFFSET,
                OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_0_OFFSET, OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_1_OFFSET,
                OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_0_OFFSET, OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_1_OFFSET,
                OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_0_OFFSET, OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_1_OFFSET,
                OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_0_OFFSET, OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_1_OFFSET,
                OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_0_OFFSET, OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_1_OFFSET,
                OTP_CTRL_SW_MANUF_PARTITION_DIGEST_0_OFFSET, OTP_CTRL_SW_MANUF_PARTITION_DIGEST_1_OFFSET,
                OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_0_OFFSET, OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_1_OFFSET,
                OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_0_OFFSET, OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_1_OFFSET,
                OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_0_OFFSET, OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_1_OFFSET,
                OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_0_OFFSET, OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_1_OFFSET,
                OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_0_OFFSET, OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_1_OFFSET,
                OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_0_OFFSET, OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_1_OFFSET,
                OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_0_OFFSET, OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_1_OFFSET
            };
        }

        fuse_ctrl_core_tl_i_write_cp: coverpoint core_tl_i.a_address[12:0] iff (core_tl_i.a_valid && core_tl_i.a_opcode == PutFullData)
        {
            bins WritableRegisters[] = {
                OTP_CTRL_INTR_STATE_OFFSET, OTP_CTRL_INTR_ENABLE_OFFSET, OTP_CTRL_INTR_TEST_OFFSET, OTP_CTRL_ALERT_TEST_OFFSET,
                OTP_CTRL_DIRECT_ACCESS_REGWEN_OFFSET, OTP_CTRL_DIRECT_ACCESS_CMD_OFFSET, OTP_CTRL_DIRECT_ACCESS_ADDRESS_OFFSET,
                OTP_CTRL_DIRECT_ACCESS_WDATA_0_OFFSET, OTP_CTRL_DIRECT_ACCESS_WDATA_1_OFFSET,
                OTP_CTRL_CHECK_TRIGGER_REGWEN_OFFSET, OTP_CTRL_CHECK_TRIGGER_OFFSET, OTP_CTRL_CHECK_REGWEN_OFFSET, OTP_CTRL_CHECK_TIMEOUT_OFFSET,
                OTP_CTRL_INTEGRITY_CHECK_PERIOD_OFFSET, OTP_CTRL_CONSISTENCY_CHECK_PERIOD_OFFSET, OTP_CTRL_SW_MANUF_PARTITION_READ_LOCK_OFFSET,
                OTP_CTRL_SVN_PARTITION_READ_LOCK_OFFSET, OTP_CTRL_VENDOR_TEST_PARTITION_READ_LOCK_OFFSET, OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_READ_LOCK_OFFSET,
                OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_READ_LOCK_OFFSET, OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK_OFFSET,
                OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_READ_LOCK_OFFSET, OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK_OFFSET
            };
        }

    endgroup

    initial begin
        fuse_ctrl_filter_cg fuse_ctrl_filter_cg1 = new();
        fuse_ctrl_test_unlock_tokens_cg fuse_ctrl_test_unlock_tokens_cg1 = new();
        fuse_ctrl_core_tl_i_cg fuse_ctrl_core_tl_i_cg1 = new();
    end

endinterface

`endif
