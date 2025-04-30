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
    wait_mci_boot_fsm_in_state(BOOT_BREAKPOINT);

    // 3. Set MCI_BOOTFSM_GO_GO_MASK to 1
    set_mci_boot_fsm_go();

    // 4. Wait for HW_FLOW_STATUS_BOOT_FSM == BOOT_WAIT_CPTRA_GO, with timeout
    wait_mci_boot_fsm_in_state(BOOT_WAIT_CPTRA_GO);

    // 5. Set CPTRA_BOOT_GO_GO_MASK to 1
    $display("[%0t] Setting CPTRA_BOOT_GO_GO_MASK to 1...", $time);
    bfm_axi_read_single_invalid_user(`SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, reg_data);
    reg_data = reg_data | `MCI_REG_CPTRA_BOOT_GO_GO_MASK;
    bfm_axi_write_single_invalid_user(`SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, reg_data);

    // 6. Wait for HW_FLOW_STATUS_BOOT_FSM == BOOT_WAIT_MCU_RST_REQ, with timeout
    wait_mci_boot_fsm_in_state(BOOT_WAIT_MCU_RST_REQ);


    $display("[%0t] smoke_test_mci_brkpoint_axi completed successfully.", $time);
    end_test_successful_req();
endtask
