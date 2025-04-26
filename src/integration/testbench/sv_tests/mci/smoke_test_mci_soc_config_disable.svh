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

task smoke_test_mci_soc_config_disable();
    // List of registers to test
    logic [AXI_AW-1:0] reg_addrs [10] = {
        `SOC_MCI_TOP_MCI_REG_FW_REV_ID_0,
        `SOC_MCI_TOP_MCI_REG_FW_REV_ID_1,
        `SOC_MCI_TOP_MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_0,
        `SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR,
        `SOC_MCI_TOP_MCI_REG_SOC_DFT_EN_0,
        `SOC_MCI_TOP_MCI_REG_SOC_DFT_EN_1,
        `SOC_MCI_TOP_MCI_REG_SOC_HW_DEBUG_EN_0,
        `SOC_MCI_TOP_MCI_REG_SOC_HW_DEBUG_EN_1,
        `SOC_MCI_TOP_MCI_REG_SOC_HW_DEBUG_EN_1,
        `SOC_MCI_TOP_MCI_REG_FC_FIPS_ZEROZATION
    };

    logic [31:0] orig_val, read_val;
    logic [31:0] test_val;

    // Wait for MCU to come out of reset
    wait_mcu_rst_b_deassert();


    for (int i = 0; i < $size(reg_addrs); i++) begin
        // Randomize test_val for each register
        assert(std::randomize(test_val));
        $display("[%t] Testing register 0x%h with randomized test_val = 0x%h", $time, reg_addrs[i], test_val);

        // Read original value
        bfm_axi_read_single(reg_addrs[i], cptra_ss_strap_mcu_lsu_axi_user_i, orig_val);

        $display("[%t] Testing caliptra dma cannot access the register", $time);
        // Try writing with caliptra_dma user
        bfm_axi_write_single_caliptra_dma(reg_addrs[i], test_val);
        bfm_axi_read_single(reg_addrs[i], cptra_ss_strap_mcu_lsu_axi_user_i, read_val);
        if (read_val !== orig_val) begin
            $error("ERROR: Register 0x%h changed after DMA user write! Was 0x%h, now 0x%h", reg_addrs[i], orig_val, read_val);
        end

        $display("[%t] Testing mci_soc_config cannot access the register", $time);
        // Try writing with mci_soc_config user
        bfm_axi_write_single(reg_addrs[i], cptra_ss_strap_mci_soc_config_axi_user_i, test_val);
        bfm_axi_read_single(reg_addrs[i], cptra_ss_strap_mcu_lsu_axi_user_i, read_val);
        if (read_val !== orig_val) begin
            $error("ERROR: Register 0x%h changed after SOC_CONFIG user write! Was 0x%h, now 0x%h", reg_addrs[i], orig_val, read_val);
        end

        $display("[%t] Testing mcu LSU can access the register", $time);
        // Try writing with mcu_lsu user
        bfm_axi_write_single_mcu_lsu(reg_addrs[i], test_val);
        bfm_axi_read_single(reg_addrs[i], cptra_ss_strap_mcu_lsu_axi_user_i, read_val);
        if (read_val !== test_val) begin
            $error("ERROR: Register 0x%h did not change after MCU_LSU user write! Was 0x%h, expected 0x%h", reg_addrs[i], read_val, test_val);
        end

        // Restore original value for next test
        bfm_axi_write_single_mcu_lsu(reg_addrs[i], orig_val);
    end

    end_test_successful_req();

endtask