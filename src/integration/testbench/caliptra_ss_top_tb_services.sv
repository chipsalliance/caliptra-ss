// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
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

`default_nettype none


module caliptra_ss_top_tb_services #(
  parameter UVM_TB = 0
) (
  input  logic        clk,
  input  logic        cptra_rst_b,
  input  logic        tb_service_cmd_valid,
  input  logic [7:0]  tb_service_cmd
);

// Instantiate the fuse controller / lifecycle testbench services submodule
fc_lcc_tb_services u_fc_lcc_tb_services (
    .clk                    (clk),
    .cptra_rst_b            (cptra_rst_b),
    .tb_service_cmd_valid   (tb_service_cmd_valid),
    .tb_service_cmd         (tb_service_cmd)
);

`include "caliptra_ss_tb_cmd_list.svh"


    logic [$bits(lc_ctrl_state_pkg::lc_state_t)-1:0] MANUF_state;
    logic [$bits(lc_ctrl_state_pkg::lc_state_t)-1:0] PROD_state;
    assign MANUF_state = lc_ctrl_state_pkg::lc_state_t'(lc_ctrl_state_pkg::LcStDev);
    assign PROD_state = lc_ctrl_state_pkg::lc_state_t'(lc_ctrl_state_pkg::LcStProd);
    initial begin
        if ($test$plusargs("CALIPTRA_SS_UDS_PROG") || $test$plusargs("CALIPTRA_SS_MANUF_DBG") || $test$plusargs("CALIPTRA_SS_PROD_DBG")) begin
            $monitor("CALIPTRA_SS_UDS_PROG: UDS_REQ is %x\n",caliptra_ss_dut.caliptra_top_dut.soc_ifc_top1.soc_ifc_reg_hwif_out.SS_DBG_MANUF_SERVICE_REG_REQ.UDS_PROGRAM_REQ.value);
            $monitor("CALIPTRA_SS_UDS_PROG: UDS_RESP IN PROGRESS is %x\n",caliptra_ss_dut.caliptra_top_dut.soc_ifc_top1.soc_ifc_reg_hwif_out.SS_DBG_MANUF_SERVICE_REG_RSP.UDS_PROGRAM_IN_PROGRESS);
            $monitor("CALIPTRA_SS_UDS_PROG: UDS_RESP UDS_PROGRAM_FAIL is %x\n",caliptra_ss_dut.caliptra_top_dut.soc_ifc_top1.soc_ifc_reg_hwif_out.SS_DBG_MANUF_SERVICE_REG_RSP.UDS_PROGRAM_FAIL);
            $monitor("CALIPTRA_SS_UDS_PROG: UDS_RESP UDS_PROGRAM_SUCCESS is %x\n",caliptra_ss_dut.caliptra_top_dut.soc_ifc_top1.soc_ifc_reg_hwif_out.SS_DBG_MANUF_SERVICE_REG_RSP.UDS_PROGRAM_SUCCESS);
            $monitor("CALIPTRA_SS_UDS_PROG: BootFSM_GO is %x\n",caliptra_ss_dut.caliptra_top_dut.soc_ifc_top1.soc_ifc_reg_hwif_out.CPTRA_BOOTFSM_GO);
            $monitor("CALIPTRA_SS_UDS_PROG: BootFSM_BrkPoint_Latched is %x\n",caliptra_ss_dut.caliptra_top_dut.soc_ifc_top1.BootFSM_BrkPoint_Latched);
            $monitor("CALIPTRA_SS_UDS_PROG: CPTRA_FLOW_STATUS is %x\n",caliptra_ss_dut.caliptra_top_dut.soc_ifc_top1.soc_ifc_reg_hwif_in.CPTRA_FLOW_STATUS);
            // force `CPTRA_SS_TB_TOP_NAME.cptra_ss_cptra_core_m_axi_if.awuser = CPTRA_SS_STRAP_CLPTRA_CORE_AXI_USER;
            force `CPTRA_SS_TB_TOP_NAME.cptra_ss_cptra_core_bootfsm_bp_i = 1'b1;
            force `CPTRA_CORE_TOP_PATH.soc_ifc_top1.soc_ifc_reg_hwif_in.CPTRA_HW_CONFIG.SUBSYSTEM_MODE_en.next = 1'b1;
        end
        if ($test$plusargs("CALIPTRA_SS_UDS_PROG")) begin
            force `MCI_PATH.from_otp_to_lcc_program_i.state = MANUF_state;
        end
        if ($test$plusargs("CALIPTRA_SS_MANUF_DBG")) begin
            force `MCI_PATH.from_otp_to_lcc_program_i.state = MANUF_state;
            force `CPTRA_CORE_TOP_PATH.soc_ifc_top1.timer1_timeout_period = 64'hFFFFFFFF_FFFFFFFF;
            force `CPTRA_SS_TB_TOP_NAME.cptra_ss_debug_intent_i = 1'b1;
        end 
        if ($test$plusargs("CALIPTRA_SS_PROD_DBG")) begin
            force `MCI_PATH.from_otp_to_lcc_program_i.state = PROD_state;
            force `CPTRA_CORE_TOP_PATH.soc_ifc_top1.timer1_timeout_period = 64'hFFFFFFFF_FFFFFFFF;
            force `CPTRA_SS_TB_TOP_NAME.cptra_ss_debug_intent_i = 1'b1;
        end 
    end

endmodule
