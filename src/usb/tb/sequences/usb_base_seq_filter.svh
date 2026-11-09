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
// Sequence-side API for the Combo and DEV1 AXI USER filter agents.
// Included inside usb_base_seq; this is not a standalone compilation unit.
//
// Each policy is an enable plus a privileged-USER allowlist on wrapper inputs,
// not DUT registers. The check_/set_ helpers send requests to both agents.
// SAMPLE only observes; SET_* changes the selected fields through the agent
// drivers at a rising bus-clock edge and checks readback at the next edge.
// Callers must drain filtered AXI traffic before changing either policy.

  // Agent readback cached by the last request, not copies of requested values.
  protected usb_combo_filter_observed_users_t combo_observed_users;
  protected usb_dev1_filter_observed_users_t dev1_observed_users;

  // ---------------------------------------------------------------------------
  // AXI USER filter policy control
  // ---------------------------------------------------------------------------

  // Fail unless the virtual sequencer carries both filter policy sequencers.
  protected function void require_filter_control();
    if (p_sequencer.combo_filter_sequencer == null || p_sequencer.dev1_filter_sequencer == null) begin
      `uvm_fatal("USB_FILTER_CTRL", "USB virtual sequencer is missing an AXI USER filter policy sequencer")
    end
  endfunction

  // Execute one request per agent concurrently and wait for both responses.
  // Each *_op selects which enable/allowlist inputs apply; SAMPLE ignores both.
  // The API sequences check SET_* readback. Return observed enables through
  // outputs and cache observed allowlists above; this does not enforce bypass.
  protected task execute_filter_agent_requests(usb_axi_user_filter_op_e combo_op, bit combo_enable, usb_combo_filter_users_t combo_users,
                                usb_axi_user_filter_op_e dev1_op, bit dev1_enable, usb_dev1_filter_users_t dev1_users,
                                output logic combo_observed_enable, output logic dev1_observed_enable);
    usb_combo_filter_api_seq_t combo_seq;
    usb_dev1_filter_api_seq_t dev1_seq;
    process caller;
    string caller_randstate;

    require_filter_control();
    // Child-sequence creation must not perturb subsequent randomized traffic.
    caller = process::self();
    caller_randstate = caller.get_randstate();
    combo_seq = usb_combo_filter_api_seq_t::type_id::create("combo_filter_api_seq");
    dev1_seq = usb_dev1_filter_api_seq_t::type_id::create("dev1_filter_api_seq");
    combo_seq.op = combo_op;
    combo_seq.enable = combo_enable;
    combo_seq.priv_axi_users = combo_users;
    dev1_seq.op = dev1_op;
    dev1_seq.enable = dev1_enable;
    dev1_seq.priv_axi_users = dev1_users;
    // Neither policy may still be updating when the caller resumes AXI traffic.
    fork
      combo_seq.start(p_sequencer.combo_filter_sequencer, this);
      dev1_seq.start(p_sequencer.dev1_filter_sequencer, this);
    join
    caller.set_randstate(caller_randstate);
    // Retain what the agents sampled, including allowlists for enable-only requests.
    combo_observed_enable = combo_seq.observed_enable;
    combo_observed_users = combo_seq.observed_priv_axi_users;
    dev1_observed_enable = dev1_seq.observed_enable;
    dev1_observed_users = dev1_seq.observed_priv_axi_users;
  endtask

  // Sample both agents and fail unless both filtering enables are known zero.
  task check_axi_user_filters_bypassed();
    usb_combo_filter_users_t combo_users;
    usb_dev1_filter_users_t dev1_users;
    logic combo_enable;
    logic dev1_enable;

    execute_filter_agent_requests(USB_AXI_USER_FILTER_SAMPLE, 1'b0, combo_users, USB_AXI_USER_FILTER_SAMPLE, 1'b0, dev1_users, combo_enable, dev1_enable);
    if (combo_enable !== 1'b0 || dev1_enable !== 1'b0) begin
      `uvm_fatal("USB_FILTER_CTRL", $sformatf("Filter enables are not known-low at start: combo=%b dev1=%b", combo_enable, dev1_enable))
    end
  endtask

  // Drive both policy enables and return once they read back as requested.
  task set_axi_user_filter_enables(bit combo_enable, bit dev1_enable);
    usb_combo_filter_users_t combo_users;
    usb_dev1_filter_users_t dev1_users;
    logic combo_observed_enable;
    logic dev1_observed_enable;

    execute_filter_agent_requests(USB_AXI_USER_FILTER_SET_ENABLE, combo_enable, combo_users, USB_AXI_USER_FILTER_SET_ENABLE, dev1_enable, dev1_users, combo_observed_enable, dev1_observed_enable);
  endtask

  // Drive both allowlists and return once every entry reads back as requested.
  task set_axi_user_allowlists(usb_combo_allowlist_t combo_users, usb_dev1_allowlist_t dev1_users);
    logic combo_observed_enable;
    logic dev1_observed_enable;

    execute_filter_agent_requests(USB_AXI_USER_FILTER_SET_USERS, 1'b0, combo_users, USB_AXI_USER_FILTER_SET_USERS, 1'b0, dev1_users, combo_observed_enable, dev1_observed_enable);
  endtask

  // Drive both enables and allowlists on the same edge.
  task set_axi_user_filter_policies(bit combo_enable, usb_combo_allowlist_t combo_users, bit dev1_enable, usb_dev1_allowlist_t dev1_users);
    logic combo_observed_enable;
    logic dev1_observed_enable;

    execute_filter_agent_requests(USB_AXI_USER_FILTER_SET_POLICY, combo_enable, combo_users, USB_AXI_USER_FILTER_SET_POLICY, dev1_enable, dev1_users, combo_observed_enable, dev1_observed_enable);
  endtask

  // Return one allowlist entry from the agents' most recent readback.
  function usb_axi_user_t axi_user_allowlist_entry(bit combo_list, int unsigned index);
    require_filter_control();
    if (combo_list) begin
      if (index >= USB_COMBO_NUM_PRIV_AXI_USERS) begin
        `uvm_fatal("USB_FILTER_CTRL", $sformatf("Combo allowlist has no entry %0d", index))
      end
      return combo_observed_users[index];
    end
    if (index >= USB_DEV1_NUM_PRIV_AXI_USERS) begin
      `uvm_fatal("USB_FILTER_CTRL", $sformatf("DEV1 allowlist has no entry %0d", index))
    end
    return dev1_observed_users[index];
  endfunction

  // Return 1 if user matches any entry of the cached Combo (combo_list=1) or DEV1 readback.
  function bit axi_user_in_allowlist(bit combo_list, usb_axi_user_t user);
    int unsigned entries;

    entries = combo_list ? USB_COMBO_NUM_PRIV_AXI_USERS : USB_DEV1_NUM_PRIV_AXI_USERS;
    for (int unsigned index = 0; index < entries; index++) begin
      if (axi_user_allowlist_entry(combo_list, index) === user) return 1'b1;
    end
    return 1'b0;
  endfunction

  // Describe both cached agent-readback allowlists for log messages.
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
