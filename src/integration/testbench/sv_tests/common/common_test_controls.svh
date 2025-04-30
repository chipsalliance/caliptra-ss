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

task end_test_successful_req();

    tb_services_if.end_test_success = 1'b1;

endtask

task wait_lcc_init();
    $display("[%t]: Waiting for LCC init", $time);
    wait(`MCI_PATH.i_boot_seqr.lc_done);
    $display("[%t]: LCC init complete", $time);
endtask

task wait_mcu_running();
    $display("[%t]: Waiting for MCU is running", $time);
    wait(`MCU_PATH.rst_l);
    $display("[%t]: MCU is running", $time);
endtask

task wait_debug_unlock();
    $display("[%t]: Waiting for debug unlock", $time);
    wait(!`MCI_PATH.LCC_state_translator.security_state_o.debug_locked);
    $display("[%t]: Debug unlock complete", $time);
endtask

task bring_ctra_core_up();
    logic [31:0] reg_data;


    $display("[%t]: Bringing up CPTRA core", $time);

    $display("[%t] Setting CPTRA FUSE DONE...", $time);
    bfm_axi_write_single_invalid_user(`SOC_SOC_IFC_REG_CPTRA_FUSE_WR_DONE, `SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK); 

    $display("[%t] Waiting for CPTRA boot FSM BOOT_DONE", $time);
    bfm_axi_read_single_invalid_user(`SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS, reg_data);     
    reg_data = (reg_data & `SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK) >> `SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_LOW;

    while(reg_data !== BOOT_DONE) begin
        bfm_axi_read_single_invalid_user(`SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS, reg_data);     
        reg_data = (reg_data & `SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK) >> `SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_LOW;

    end

    $display("[%t]: CPTRA core up", $time);
endtask