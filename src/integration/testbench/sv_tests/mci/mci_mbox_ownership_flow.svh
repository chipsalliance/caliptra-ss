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
// MCI_MBOX0/1_OWNERSHIP_FLOW: basic SoC Requester -> MCU (Root) -> SoC Target flow on one MCU mailbox,
// with the AXI BFM driving all three agents after boot.
//
// Each transaction walks every SRAM ownership hand-off (HW spec "MCU Mailbox SRAM Ownership"):
//--------------------------------------------------------------------------------------------------
//   phase                     SRAM/DLEN owner   moved there by
//--------------------------------------------------------------------------------------------------
//   requester-staged          Requester         LOCK read returning 0
//   root-owns-request         Root              Requester EXECUTE=1 (CMD_AVAIL to Root)
//   target-owns-request       Target            Root TARGET_USER, then TARGET_USER_VALID=1
//   root-owns-response        Root              Target terminal TARGET_STATUS (TARGET_DONE to Root)
//   requester-owns-response   Requester         Root non-BUSY CMD_STATUS
//   released                  none              SRAM owner EXECUTE=0 (wipe, then LOCK free)
//--------------------------------------------------------------------------------------------------
// At every phase each non-owner reads up to three random payload words as 0, and its writes to them and its EXECUTE=0
// are dropped.
// After each release the Requester re-acquires LOCK and checks every SRAM word the transaction used was wiped.
// One transaction per terminal status (DATA_READY, CMD_COMPLETE, CMD_FAILURE), with random lengths and CMD.
// Then one aborted transaction per owned phase before the response, in random order: that phase's SRAM owner ends it
// early with EXECUTE=0 (HW spec "MCU Mailbox Locking": only the SRAM owner may release).

localparam int MCI_COMM_FLOW_MAX_DLEN = 64;

int mci_comm_flow_mbox;
logic [31:0] mci_comm_flow_requester, mci_comm_flow_root, mci_comm_flow_target;
logic [AXI_AW-1:0] mci_comm_flow_cmd_addr, mci_comm_flow_dlen_addr, mci_comm_flow_execute_addr,
                   mci_comm_flow_target_user_addr, mci_comm_flow_target_valid_addr, mci_comm_flow_target_status_addr,
                   mci_comm_flow_cmd_status_addr, mci_comm_flow_sram;
// Expected SRAM contents of the current transaction, by word.
logic [31:0] mci_comm_flow_payload [$];

// `user`, as SRAM owner, overwrites the first words with fresh non-zero data and sets a random DLEN covering them.
task automatic mci_comm_flow_write_data(input logic [31:0] user);
    int len = $urandom_range(1, MCI_COMM_FLOW_MAX_DLEN);
    logic [31:0] word;
    for (int i = 0; i < (len + 3) / 4; i++) begin
        word = $urandom() | 32'h0101_0101;
        if (i < mci_comm_flow_payload.size()) mci_comm_flow_payload[i] = word;
        else mci_comm_flow_payload.push_back(word);
        mcu_mbox_write(mci_comm_flow_sram + 4*i, user, word);
    end
    mcu_mbox_write(mci_comm_flow_dlen_addr, user, len);
endtask

// At up to three payload words, re-picked on every call, every other agent must read SRAM as 0 and have its SRAM
// write dropped (the owner, if any, still reads its own data). Every other agent's EXECUTE=0 must be dropped too, so
// HW_STATUS must still report `owner` afterwards.
task automatic mci_comm_flow_check_phase(input string phase, input mcu_mbox_sram_owner_e owner);
    logic [AXI_AW-1:0] addr;
    logic [31:0] users [4];
    int words [$];
    users = '{'0, mci_comm_flow_requester, mci_comm_flow_root, mci_comm_flow_target};  // indexed by sram_owner code
    for (int i = 0; i < mci_comm_flow_payload.size(); i++) words.push_back(i);
    words.shuffle();
    while (words.size() > 3) void'(words.pop_back());
    $display("[%0t] MCI_COMM_FLOW mbox=%0d phase=%s sram_owner=%s words=%p", $time, mci_comm_flow_mbox, phase,
             owner.name(), words);
    for (int agent = MCU_MBOX_OWNER_REQUESTER; agent <= MCU_MBOX_OWNER_TARGET; agent++)
        if (agent != owner) begin
            foreach (words[i]) begin
                addr = mci_comm_flow_sram + 4*words[i];
                mcu_mbox_read_check(addr, users[agent], 0);
                mcu_mbox_write(addr, users[agent], ~mci_comm_flow_payload[words[i]]);
                if (owner != MCU_MBOX_OWNER_NONE)
                    mcu_mbox_read_check(addr, users[owner], mci_comm_flow_payload[words[i]]);
            end
            mcu_mbox_write(mci_comm_flow_execute_addr, users[agent], 0);
        end
    mcu_mbox_check_sram_owner(mci_comm_flow_mbox, owner, {"MCI_COMM_FLOW ", phase});
endtask

// `user`, the current SRAM owner, ends the transaction with EXECUTE=0: no owner during the wipe or while LOCK is free.
// The Requester then re-acquires LOCK, and every SRAM word the transaction used must have been wiped.
task automatic mci_comm_flow_end(input logic [31:0] user);
    mcu_mbox_write(mci_comm_flow_execute_addr, user, 0);
    mci_comm_flow_check_phase("released", MCU_MBOX_OWNER_NONE);
    mcu_mbox_acquire_lock(mci_comm_flow_mbox, mci_comm_flow_requester);
    foreach (mci_comm_flow_payload[i]) mcu_mbox_read_check(mci_comm_flow_sram + 4*i, mci_comm_flow_requester, 0);
    mci_comm_flow_payload = {};
endtask

// One Requester -> Root -> Target -> Root -> Requester transaction ending in `status`. If `abort_at` names a phase,
// that phase's SRAM owner ends the transaction there instead.
// The Requester holds LOCK on entry, and again on exit after re-acquiring it to check the wipe.
task automatic mci_comm_flow_transaction(input logic [31:0] status, input string abort_at = "");
    logic [31:0] cmd = $urandom_range(1, 32'hFFFF_FFFF);
    $display("[%0t] MCI_COMM_FLOW mbox=%0d transaction status=%0d cmd=%08x abort_at=%s", $time, mci_comm_flow_mbox,
             status, cmd, abort_at);

    // Requester stages CMD, the request and DLEN.
    mcu_mbox_write(mci_comm_flow_cmd_addr, mci_comm_flow_requester, cmd);
    mci_comm_flow_write_data(mci_comm_flow_requester);
    mci_comm_flow_check_phase("requester-staged", MCU_MBOX_OWNER_REQUESTER);
    if (abort_at == "requester-staged") begin mci_comm_flow_end(mci_comm_flow_requester); return; end

    // EXECUTE=1 hands the SRAM to Root, which is notified by CMD_AVAIL.
    mcu_mbox_write(mci_comm_flow_execute_addr, mci_comm_flow_requester, 1);
    mcu_mbox_wait_clear_notif(mci_comm_flow_mbox, MCU_MBOX_NOTIF_CMD_AVAIL);
    mci_comm_flow_check_phase("root-owns-request", MCU_MBOX_OWNER_ROOT);
    if (abort_at == "root-owns-request") begin mci_comm_flow_end(mci_comm_flow_root); return; end

    // Root names the Target; TARGET_USER_VALID=1 hands it the SRAM. Root then notifies the Target over a sideband
    // outside the subsystem, emulated here as a short random delay before the Target proceeds.
    mcu_mbox_write(mci_comm_flow_target_user_addr, mci_comm_flow_root, mci_comm_flow_target);
    mcu_mbox_write(mci_comm_flow_target_valid_addr, mci_comm_flow_root, 1);
    mci_comm_flow_check_phase("target-owns-request", MCU_MBOX_OWNER_TARGET);
    repeat ($urandom_range(1, 16)) @(posedge core_clk);
    if (abort_at == "target-owns-request") begin mci_comm_flow_end(mci_comm_flow_target); return; end

    // Target writes its response and DLEN; a terminal TARGET_STATUS returns the SRAM to Root with TARGET_DONE.
    mci_comm_flow_write_data(mci_comm_flow_target);
    mcu_mbox_write(mci_comm_flow_target_status_addr, mci_comm_flow_target, status);
    mcu_mbox_wait_clear_notif(mci_comm_flow_mbox, MCU_MBOX_NOTIF_TARGET_DONE);
    mci_comm_flow_check_phase("root-owns-response", MCU_MBOX_OWNER_ROOT);
    if (abort_at == "root-owns-response") begin mci_comm_flow_end(mci_comm_flow_root); return; end

    // Root finalizes the response and DLEN; a non-BUSY CMD_STATUS returns the SRAM to the Requester.
    mci_comm_flow_write_data(mci_comm_flow_root);
    mcu_mbox_write(mci_comm_flow_cmd_status_addr, mci_comm_flow_root, status);
    mci_comm_flow_check_phase("requester-owns-response", MCU_MBOX_OWNER_REQUESTER);
    mci_comm_flow_end(mci_comm_flow_requester);
endtask

task automatic mci_comm_flow_body(input int mbox_num);
    logic [31:0] soc_users [$];
    string abort_points [$] = '{"requester-staged", "root-owns-request", "target-owns-request", "root-owns-response"};
    mci_comm_flow_mbox = mbox_num;
    mci_boot_mcu_and_caliptra();

    // Requester and Target are random trusted SoC users; Root is the MCU.
    mcu_mbox_pick_soc_users(soc_users, 2);
    mci_comm_flow_requester = soc_users[0];
    mci_comm_flow_root = cptra_ss_strap_mcu_lsu_axi_user_i;
    mci_comm_flow_target = soc_users[1];
    $display("MCI_COMM_FLOW setup mbox=%0d requester=%08x root=%08x target=%08x",
             mbox_num, mci_comm_flow_requester, mci_comm_flow_root, mci_comm_flow_target);

    get_mcu_mbox_cmd_addr(mci_comm_flow_cmd_addr, mbox_num);
    get_mcu_mbox_dlen_addr(mci_comm_flow_dlen_addr, mbox_num);
    get_mbox_mcu_execute_addr(mci_comm_flow_execute_addr, mbox_num);
    get_mcu_mbox_target_user_addr(mci_comm_flow_target_user_addr, mbox_num);
    get_mcu_mbox_target_user_valid_addr(mci_comm_flow_target_valid_addr, mbox_num);
    get_mcu_mbox_target_status_addr(mci_comm_flow_target_status_addr, mbox_num);
    get_mbox_mcu_cmd_status_addr(mci_comm_flow_cmd_status_addr, mbox_num);
    get_mcu_mbox_sram_base_addr(mci_comm_flow_sram, mbox_num);

    mcu_mbox_set_trusted_users(mbox_num, soc_users);
    mcu_mbox_release(mbox_num, mci_comm_flow_root);  // Root holds LOCK out of reset
    mcu_mbox_acquire_lock(mbox_num, mci_comm_flow_requester);
    mcu_mbox_wait_clear_notif(mbox_num, MCU_MBOX_NOTIF_CMD_AVAIL, .do_wait(0));
    mcu_mbox_wait_clear_notif(mbox_num, MCU_MBOX_NOTIF_TARGET_DONE, .do_wait(0));

    for (int status = mcu_mbox_csr__mbox_cmd_status__status__mbox_status_e__DATA_READY;
         status <= mcu_mbox_csr__mbox_cmd_status__status__mbox_status_e__CMD_FAILURE; status++)
        mci_comm_flow_transaction(status);
    abort_points.shuffle();
    foreach (abort_points[i])
        mci_comm_flow_transaction($urandom_range(mcu_mbox_csr__mbox_cmd_status__status__mbox_status_e__DATA_READY,
                                           mcu_mbox_csr__mbox_cmd_status__status__mbox_status_e__CMD_FAILURE),
                            abort_points[i]);

    mcu_mbox_release(mbox_num, mci_comm_flow_requester);

    if (mcu_mbox_err_cnt != 0 || `CPTRA_SS_TOP_PATH.cptra_ss_all_error_fatal_o !== 0) begin
        $fatal(1, "* TESTCASE FAILED: Error Count: %0d, cptra_ss_all_error_fatal_o=%0b",
               mcu_mbox_err_cnt, `CPTRA_SS_TOP_PATH.cptra_ss_all_error_fatal_o);
    end else begin
        end_test_successful_req();
    end
endtask

// Test entry points, selected by +cptra_ss_sv_test=MCI_MBOX0/1_OWNERSHIP_FLOW.
task automatic mci_mbox0_ownership_flow();
    mci_comm_flow_body(0);
endtask

task automatic mci_mbox1_ownership_flow();
    mci_comm_flow_body(1);
endtask
