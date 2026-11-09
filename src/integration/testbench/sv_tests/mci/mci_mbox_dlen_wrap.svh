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
// MCU mailbox release wipe vs. DLEN larger than the mailbox SRAM.
// HW spec "MCU Mailbox SRAM Clearing": on release the SRAM is zeroed from 0 to the
// max DLEN set during the lock. This test stages a pattern, sets DLEN, releases,
// re-acquires and checks the staged words were zeroed. Root (MCU LSU user) holds
// the reset LOCK, so it acts as the Requester throughout.

localparam int MCI_MDW_WORDS = 16;

// Stage a pattern, set DLEN, release, re-acquire, and count staged words that survived the wipe.
task automatic mci_mdw_run(input int mbox_num, input string name, input logic [31:0] dlen,
                           input logic [31:0] size_bytes, output int leftover);
    logic [AXI_AW-1:0] lock_addr, user_addr, dlen_addr, execute_addr, sram;
    logic [31:0] data, pattern;
    int expected_wiped_words;
    bit acquired;

    get_mcu_mbox_lock_address(lock_addr, mbox_num);
    get_mcu_mbox_user_addr(user_addr, mbox_num);
    get_mcu_mbox_dlen_addr(dlen_addr, mbox_num);
    get_mbox_mcu_execute_addr(execute_addr, mbox_num);
    get_mcu_mbox_sram_base_addr(sram, mbox_num);

    mcu_mbox_read_check(user_addr, cptra_ss_strap_mcu_lsu_axi_user_i, cptra_ss_strap_mcu_lsu_axi_user_i);

    for (int i = 0; i < MCI_MDW_WORDS; i++) begin
        pattern = 32'hA500_0000 | (mbox_num << 16) | i;
        bfm_axi_write_single_mcu_lsu(sram + 4*i, pattern);
        mcu_mbox_read_check(sram + 4*i, cptra_ss_strap_mcu_lsu_axi_user_i, pattern);
    end
    bfm_axi_write_single_mcu_lsu(dlen_addr, dlen);
    mcu_mbox_read_check(dlen_addr, cptra_ss_strap_mcu_lsu_axi_user_i, dlen);

    // Spec: the wipe covers 0..DLEN, capped at the end of the SRAM.
    expected_wiped_words = (dlen >= size_bytes) ? (size_bytes >> 2) : (((dlen - 1) >> 2) + 1);
    $display("[%0t] MCI_MDW mbox=%0d case=%s dlen=0x%08x sram_size=0x%08x staged_words=%0d expected_wiped_words=%0d",
             $time, mbox_num, name, dlen, size_bytes, MCI_MDW_WORDS, expected_wiped_words);

    // Release; the wipe holds LOCK=1, then the next LOCK read of 0 re-acquires for Root.
    bfm_axi_write_single_mcu_lsu(execute_addr, 0);
    acquired = 0;
    for (int attempt = 0; attempt < 100000; attempt++) begin
        bfm_axi_read_single_mcu_lsu(lock_addr, data);
        if (data === 0) begin
            acquired = 1;
            break;
        end
        repeat (8) @(posedge core_clk);
    end
    if (!acquired)
        $fatal(1, "MCI_MDW mbox=%0d case=%s timed out re-acquiring LOCK", mbox_num, name);

    leftover = 0;
    for (int i = 0; i < MCI_MDW_WORDS; i++) begin
        bfm_axi_read_single_mcu_lsu(sram + 4*i, data);
        if (data !== 0) begin
            leftover++;
            $display("MCI_MDW mbox=%0d case=%s word=%0d NOT WIPED: 0x%08x", mbox_num, name, i, data);
        end
    end
    $display("[%0t] MCI_MDW RESULT mbox=%0d case=%s dlen=0x%08x zeroed=%0d/%0d leftover=%0d -> %s",
             $time, mbox_num, name, dlen, MCI_MDW_WORDS - leftover, MCI_MDW_WORDS, leftover,
             leftover ? "FAIL" : "PASS");
endtask

// Entry point, selected by +cptra_ss_sv_test=MCI_MBOX_DLEN_WRAP. Runs both mailboxes.
task automatic mci_mbox_dlen_wrap();
    logic [31:0] hw_config, size_bytes;
    int leftover, failures;

    mci_boot_mcu_and_caliptra();

    bfm_axi_read_single_mcu_lsu(`SOC_MCI_TOP_MCI_REG_HW_CONFIG0, hw_config);
    failures = 0;
    for (int mbox_num = 0; mbox_num < 2; mbox_num++) begin
        size_bytes = 1024 * (mbox_num ?
            ((hw_config & `MCI_REG_HW_CONFIG0_MCU_MBOX1_SRAM_SIZE_MASK) >> `MCI_REG_HW_CONFIG0_MCU_MBOX1_SRAM_SIZE_LOW) :
            ((hw_config & `MCI_REG_HW_CONFIG0_MCU_MBOX0_SRAM_SIZE_MASK) >> `MCI_REG_HW_CONFIG0_MCU_MBOX0_SRAM_SIZE_LOW));
        if (size_bytes < 4*MCI_MDW_WORDS)
            $fatal(1, "MCI_MDW mbox=%0d SRAM size %0d bytes too small", mbox_num, size_bytes);

        // Controls: DLEN covering the staged words, and DLEN equal to the SRAM size.
        mci_mdw_run(mbox_num, "IN_RANGE", 4*MCI_MDW_WORDS, size_bytes, leftover);
        if (leftover) failures++;
        mci_mdw_run(mbox_num, "EQ_SIZE", size_bytes, size_bytes, leftover);
        if (leftover) failures++;
        // Spec: zero 0..DLEN, so every staged word must be cleared.
        mci_mdw_run(mbox_num, "SIZE_PLUS_8", size_bytes + 8, size_bytes, leftover);
        if (leftover) failures++;
    end

    if (failures || mcu_mbox_err_cnt != 0)
        $fatal(1, "* TESTCASE FAILED: MCI_MDW %0d release(s) left staged data in SRAM, Error Count: %0d",
               failures, mcu_mbox_err_cnt);
    $display("MCI_MDW PASS: every release zeroed the staged words");

    end_test_successful_req();
endtask
