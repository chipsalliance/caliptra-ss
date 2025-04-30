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


task smoke_test_mcu_no_rom_config_brkpoint();
    $display("[%0t] Starting SMOKE_TEST_MCU_NO_ROM_CONFIG_BRKPOINT sequence...", $time);

    wait_mci_rst_b_deassert();
    
    wait_mci_boot_fsm_in_state(BOOT_BREAKPOINT);

    set_mci_boot_fsm_go();
    
    wait_mci_boot_fsm_in_state(BOOT_WAIT_CPTRA_GO);

    $display("[%0t] Setting CPTRA_BOOT_GO_GO_MASK to 1...", $time);
    bfm_axi_write_single_invalid_user(`SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, `MCI_REG_CPTRA_BOOT_GO_GO_MASK); 

    bring_ctra_core_up();

    wait_for_mcu_reset_req_and_clear();

    request_mcu_reset();

    mcu_halt_handshake();

    wait_mcu_in_reset();

    wait_mcu_out_of_reset();

    $display("[%0t] SMOKE_TEST_MCU_NO_ROM_CONFIG_BRKPOINT sequence done. MCU will end test...", $time);

endtask
