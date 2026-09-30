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

// Basic subsystem connectivity check for the USB AXI USER filters. One location on
// each of the four independently wired converter paths is accessed with every
// allowed USER (expect OKAY and matching readback) and with two USERs that are in
// neither allowlist (expect SLVERR, zero read data, and an unchanged location).
// Single-beat accesses only; USB enumeration is not needed for bus-side access.
// The MCU and Caliptra firmware stay idle so they cannot touch these locations.

task automatic smoke_test_usb_axi_filter_path(input usb_axi_filter_path_e path,
                                               input logic [31:0]         invalid_users [USB_AXI_FILTER_NUM_INVALID_USERS]);
    string       who;
    logic [31:0] mask;
    logic [31:0] ref_user;
    logic [31:0] user;
    logic [31:0] original;
    logic [31:0] expected;
    logic [31:0] data;
    logic [31:0] rd_data;

    mask     = usb_axi_filter_path_mask(path);
    // Authorized USER for setup, restore, and preservation rereads.
    ref_user = usb_axi_filter_allowed_user(path, 0);

    $display("[%t] ==== USB AXI FILTER: %s @ 0x%08h ====", $time, usb_axi_filter_path_name(path), usb_axi_filter_path_addr(path));

    // Setup: the CSR value is saved for restore. SRAM reset contents are undefined,
    // so a known baseline is written and verified first.
    if (usb_axi_filter_path_is_csr(path)) begin
        usb_axi_filter_read(path, "setup", ref_user, '0, '0, AXI_RESP_OKAY, original);
    end else begin
        original = $urandom();
        usb_axi_filter_write(path, "setup", ref_user, original, AXI_RESP_OKAY);
        usb_axi_filter_read(path, "setup", ref_user, original, mask, AXI_RESP_OKAY, rd_data);
    end
    expected = original;

    // Allowed USERs: each slot writes a value that differs from the current contents,
    // so every accepted write is observable on readback.
    for (int unsigned s = 0; s < usb_axi_filter_num_allowed_users(path); s++) begin
        who  = $sformatf("allowed slot %0d", s);
        user = usb_axi_filter_allowed_user(path, s);
        do data = $urandom(); while (((data ^ expected) & mask) == '0);
        usb_axi_filter_write(path, who, user, data, AXI_RESP_OKAY);
        usb_axi_filter_read(path, who, user, data, mask, AXI_RESP_OKAY, rd_data);
        expected = data;
    end

    // Invalid USERs: each rejected write carries a distinct value that differs from
    // the current contents in every bit, and an authorized reread proves it never
    // reached the location. The rejected read must return SLVERR with zero data.
    for (int i = 0; i < USB_AXI_FILTER_NUM_INVALID_USERS; i++) begin
        who  = $sformatf("invalid %0d", i);
        data = ~expected ^ (32'h0f0f_0f0f * i);
        usb_axi_filter_write(path, who, invalid_users[i], data, AXI_RESP_SLVERR);
        usb_axi_filter_read(path, {who, " preservation reread"}, ref_user, expected, mask, AXI_RESP_OKAY, rd_data);
        usb_axi_filter_read(path, who, invalid_users[i], '0, 32'hffff_ffff, AXI_RESP_SLVERR, rd_data);
    end

    // Restore: the CSR returns to its original value; SRAM keeps the last allowed value.
    if (usb_axi_filter_path_is_csr(path)) begin
        usb_axi_filter_write(path, "restore", ref_user, original, AXI_RESP_OKAY);
        usb_axi_filter_read(path, "restore", ref_user, original, mask, AXI_RESP_OKAY, rd_data);
    end
endtask

task automatic smoke_test_usb_axi_filter();
    logic [31:0] invalid_users [USB_AXI_FILTER_NUM_INVALID_USERS];

    $display("[%t] ==== SMOKE_TEST_USB_AXI_FILTER: start ====", $time);
    wait_mcu_rst_b_deassert();

    // Configuration: this test needs both filters enabled with the TB's two-entry lists.
    if (!usb_axi_user_policy_is_ready())
        $fatal(1, "[%t] SMOKE_TEST_USB_AXI_FILTER: USB AXI USER policy was not initialized", $time);
    if ((cptra_ss_usb_combo_enable_axi_user_filtering_i !== 1'b1) || (cptra_ss_usb_dev1_enable_axi_user_filtering_i !== 1'b1))
        $fatal(1, "[%t] SMOKE_TEST_USB_AXI_FILTER: requires both USB AXI USER filters enabled (Combo=%b DEV1=%b)",
               $time, cptra_ss_usb_combo_enable_axi_user_filtering_i, cptra_ss_usb_dev1_enable_axi_user_filtering_i);
    if ((USB_COMBO_NUM_PRIV_AXI_USERS != 2) || (USB_DEV1_NUM_PRIV_AXI_USERS != 2))
        $fatal(1, "[%t] SMOKE_TEST_USB_AXI_FILTER: expected 2 allowlist entries per policy (Combo=%0d DEV1=%0d)",
               $time, USB_COMBO_NUM_PRIV_AXI_USERS, USB_DEV1_NUM_PRIV_AXI_USERS);

    $display("[%t] ==== SMOKE_TEST_USB_AXI_FILTER: resolved policy ====", $time);
    usb_axi_user_policy_print();
    usb_axi_filter_get_invalid_users(invalid_users);

    usb_axi_filter_err_cnt   = 0;
    usb_axi_filter_check_cnt = 0;
    for (int p = 0; p < USB_AXI_FILTER_NUM_PATHS; p++)
        smoke_test_usb_axi_filter_path(usb_axi_filter_path_e'(p), invalid_users);

    $display("[%t] ==== SMOKE_TEST_USB_AXI_FILTER: %0d paths, %0d invalid USERs per path, %0d checks, %0d errors ====",
             $time, USB_AXI_FILTER_NUM_PATHS, USB_AXI_FILTER_NUM_INVALID_USERS, usb_axi_filter_check_cnt, usb_axi_filter_err_cnt);
    if (usb_axi_filter_err_cnt != 0)
        $fatal(1, "[%t] SMOKE_TEST_USB_AXI_FILTER: %0d of %0d checks failed", $time, usb_axi_filter_err_cnt, usb_axi_filter_check_cnt);

    end_test_successful_req();
endtask
