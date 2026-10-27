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
// AXI USER filter utilities for usb_base_seq. This file is included inside the
// usb_base_seq class body and is not compiled on its own.
//
// The filter enables and allowlists are wrapper inputs driven by the bench
// through usb_tb_ctrl_if, not DUT registers. Every helper changes them with
// nonblocking assignments at a rising clock edge and confirms the change at
// the next edge. Callers must have no AXI request in flight while a policy
// changes.

  // ---------------------------------------------------------------------------
  // AXI USER filter policy control
  // ---------------------------------------------------------------------------

  // Fail unless the virtual sequencer carries the filter control interface.
  protected function void require_filter_control();
    if (p_sequencer.ctrl_vif == null) begin
      `uvm_fatal("USB_FILTER_CTRL", "USB virtual sequencer is missing the AXI USER filter control VIF")
    end
  endfunction

  // Require both policies to hold usb_top_tb's known-low bypass default at the
  // next rising edge, so a filter scenario starts from a known state.
  task check_axi_user_filters_bypassed();
    require_filter_control();
    @(posedge p_sequencer.ctrl_vif.clk);
    if (p_sequencer.ctrl_vif.combo_enable_axi_user_filtering !== 1'b0 ||
        p_sequencer.ctrl_vif.dev1_enable_axi_user_filtering !== 1'b0) begin
      `uvm_fatal("USB_FILTER_CTRL", $sformatf("Filter enables are not known-low at start: combo=%b dev1=%b", p_sequencer.ctrl_vif.combo_enable_axi_user_filtering, p_sequencer.ctrl_vif.dev1_enable_axi_user_filtering))
    end
  endtask

  // Drive both policy enables and return once they read back as requested.
  task set_axi_user_filter_enables(bit combo_enable, bit dev1_enable);
    require_filter_control();
    @(posedge p_sequencer.ctrl_vif.clk);
    p_sequencer.ctrl_vif.combo_enable_axi_user_filtering <= combo_enable;
    p_sequencer.ctrl_vif.dev1_enable_axi_user_filtering <= dev1_enable;
    @(posedge p_sequencer.ctrl_vif.clk);
    if (p_sequencer.ctrl_vif.combo_enable_axi_user_filtering !== combo_enable ||
        p_sequencer.ctrl_vif.dev1_enable_axi_user_filtering !== dev1_enable) begin
      `uvm_fatal("USB_FILTER_CTRL", $sformatf("Filter enables read back combo=%b dev1=%b, expected %0b/%0b", p_sequencer.ctrl_vif.combo_enable_axi_user_filtering, p_sequencer.ctrl_vif.dev1_enable_axi_user_filtering, combo_enable, dev1_enable))
    end
  endtask

  // Drive both allowlists and return once every entry reads back as requested.
  task set_axi_user_allowlists(usb_combo_allowlist_t combo_users, usb_dev1_allowlist_t dev1_users);
    require_filter_control();
    @(posedge p_sequencer.ctrl_vif.clk);
    foreach (combo_users[index]) p_sequencer.ctrl_vif.combo_priv_axi_users[index] <= combo_users[index];
    foreach (dev1_users[index]) p_sequencer.ctrl_vif.dev1_priv_axi_users[index] <= dev1_users[index];
    @(posedge p_sequencer.ctrl_vif.clk);
    foreach (combo_users[index]) begin
      if (p_sequencer.ctrl_vif.combo_priv_axi_users[index] !== combo_users[index]) begin
        `uvm_fatal("USB_FILTER_CTRL", $sformatf("Combo allowlist entry %0d read back 0x%0h, expected 0x%0h", index, p_sequencer.ctrl_vif.combo_priv_axi_users[index], combo_users[index]))
      end
    end
    foreach (dev1_users[index]) begin
      if (p_sequencer.ctrl_vif.dev1_priv_axi_users[index] !== dev1_users[index]) begin
        `uvm_fatal("USB_FILTER_CTRL", $sformatf("DEV1 allowlist entry %0d read back 0x%0h, expected 0x%0h", index, p_sequencer.ctrl_vif.dev1_priv_axi_users[index], dev1_users[index]))
      end
    end
  endtask

  // Return one allowlist entry as currently driven, i.e. what the DUT sees.
  function usb_axi_user_t axi_user_allowlist_entry(bit combo_list, int unsigned index);
    require_filter_control();
    if (combo_list) begin
      if (index >= USB_COMBO_NUM_PRIV_AXI_USERS) begin
        `uvm_fatal("USB_FILTER_CTRL", $sformatf("Combo allowlist has no entry %0d", index))
      end
      return p_sequencer.ctrl_vif.combo_priv_axi_users[index];
    end
    if (index >= USB_DEV1_NUM_PRIV_AXI_USERS) begin
      `uvm_fatal("USB_FILTER_CTRL", $sformatf("DEV1 allowlist has no entry %0d", index))
    end
    return p_sequencer.ctrl_vif.dev1_priv_axi_users[index];
  endfunction

  // Return 1 if user matches any currently driven entry of the Combo
  // (combo_list=1) or DEV1 allowlist.
  function bit axi_user_in_allowlist(bit combo_list, usb_axi_user_t user);
    int unsigned entries;

    entries = combo_list ? USB_COMBO_NUM_PRIV_AXI_USERS : USB_DEV1_NUM_PRIV_AXI_USERS;
    for (int unsigned index = 0; index < entries; index++) begin
      if (axi_user_allowlist_entry(combo_list, index) === user) return 1'b1;
    end
    return 1'b0;
  endfunction

  // Describe both driven allowlists for log messages.
  function string format_axi_user_allowlists();
    string combo_text;
    string dev1_text;

    for (int unsigned index = 0; index < USB_COMBO_NUM_PRIV_AXI_USERS; index++) begin
      combo_text = {combo_text, $sformatf(" 0x%08h", axi_user_allowlist_entry(1'b1, index))};
    end
    for (int unsigned index = 0; index < USB_DEV1_NUM_PRIV_AXI_USERS; index++) begin
      dev1_text = {dev1_text, $sformatf(" 0x%08h", axi_user_allowlist_entry(1'b0, index))};
    end
    return $sformatf("Combo =%s; DEV1 =%s", combo_text, dev1_text);
  endfunction
