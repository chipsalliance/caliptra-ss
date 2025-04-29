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

task automatic smoke_test_mci_brkpoint_axi();
    // Local variables
    logic [31:0] reg_data;
    int i;

    // 1. Wait for MCI to come out of reset
    $display("[%0t] Waiting for MCI to come out of reset...", $time);
    wait_mci_rst_b_deassert();
    $display("[%0t] MCI out of reset.", $time);

    // 2. Wait for HW_FLOW_STATUS_BOOT_FSM == 4'h4, with timeout
    $display("[%0t] Waiting for HW_FLOW_STATUS_BOOT_FSM == BOOT_BREAKPOINT...", $time);
    for (i = 0; i < 100000; i++) begin
        bfm_axi_read_single_invalid_user(`SOC_MCI_TOP_MCI_REG_HW_FLOW_STATUS, reg_data);
        if ((reg_data & `MCI_REG_HW_FLOW_STATUS_BOOT_FSM_MASK) == BOOT_BREAKPOINT) begin
            $display("[%0t] HW_FLOW_STATUS_BOOT_FSM == BOOT_BREAKPOINT detected.", $time);
            break;
        end
    end
    if (i == 100000) begin
        $fatal(1, "[%0t] FATAL: Timeout waiting for HW_FLOW_STATUS_BOOT_FSM == BOOT_BREAKPOINT", $time);
    end

    // 3. Set MCI_BOOTFSM_GO_GO_MASK to 1
    $display("[%0t] Setting MCI_BOOTFSM_GO_GO_MASK to 1...", $time);
    bfm_axi_read_single_invalid_user(`SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO, reg_data);
    reg_data = reg_data | `MCI_REG_MCI_BOOTFSM_GO_GO_MASK;
    bfm_axi_write_single_invalid_user(`SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO, reg_data);

    // 4. Wait for HW_FLOW_STATUS_BOOT_FSM == BOOT_WAIT_CPTRA_GO, with timeout
    $display("[%0t] Waiting for HW_FLOW_STATUS_BOOT_FSM == BOOT_WAIT_CPTRA_GO...", $time);
    for (i = 0; i < 100000; i++) begin
        bfm_axi_read_single_invalid_user(`SOC_MCI_TOP_MCI_REG_HW_FLOW_STATUS, reg_data);
        if ((reg_data & `MCI_REG_HW_FLOW_STATUS_BOOT_FSM_MASK) == BOOT_WAIT_CPTRA_GO) begin
            $display("[%0t] HW_FLOW_STATUS_BOOT_FSM == BOOT_WAIT_CPTRA_GO detected.", $time);
            break;
        end
    end
    if (i == 100000) begin
        $fatal(1, "[%0t] FATAL: Timeout waiting for HW_FLOW_STATUS_BOOT_FSM == BOOT_WAIT_CPTRA_GO", $time);
    end

    // 5. Set CPTRA_BOOT_GO_GO_MASK to 1
    $display("[%0t] Setting CPTRA_BOOT_GO_GO_MASK to 1...", $time);
    bfm_axi_read_single_invalid_user(`SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, reg_data);
    reg_data = reg_data | `MCI_REG_CPTRA_BOOT_GO_GO_MASK;
    bfm_axi_write_single_invalid_user(`SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, reg_data);

    // 6. Wait for HW_FLOW_STATUS_BOOT_FSM == BOOT_WAIT_MCU_RST_REQ, with timeout
    $display("[%0t] Waiting for HW_FLOW_STATUS_BOOT_FSM == BOOT_WAIT_MCU_RST_REQ...", $time);
    for (i = 0; i < 100000; i++) begin
        bfm_axi_read_single_invalid_user(`SOC_MCI_TOP_MCI_REG_HW_FLOW_STATUS, reg_data);
        if ((reg_data & `MCI_REG_HW_FLOW_STATUS_BOOT_FSM_MASK) == BOOT_WAIT_MCU_RST_REQ) begin
            $display("[%0t] HW_FLOW_STATUS_BOOT_FSM == BOOT_WAIT_MCU_RST_REQ detected.", $time);
            break;
        end
    end
    if (i == 100000) begin
        $fatal(1, "[%0t] FATAL: Timeout waiting for HW_FLOW_STATUS_BOOT_FSM == BOOT_WAIT_MCU_RST_REQ", $time);
    end

    $display("[%0t] smoke_test_mci_brkpoint_axi completed successfully.", $time);
    end_test_successful_req();
endtask
