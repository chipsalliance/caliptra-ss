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

// A controllable register response exercises the real shared access helpers
// without hanging the DUT or leaving its bus in an incomplete transaction.
class usb_delayed_reg extends uvm_reg;
  `uvm_object_utils(usb_delayed_reg)

  realtime response_delay;
  uvm_reg_data_t response_value = 1;

  function new(string name = "usb_delayed_reg");
    super.new(name, 32, UVM_NO_COVERAGE);
  endfunction

  virtual task read(
    output uvm_status_e status, output uvm_reg_data_t value,
    input uvm_path_e path = UVM_DEFAULT_PATH, input uvm_reg_map map = null,
    input uvm_sequence_base parent = null, input int prior = -1,
    input uvm_object extension = null, input string fname = "",
    input int lineno = 0
  );
    #(response_delay);
    status = UVM_IS_OK;
    value = response_value;
  endtask

  virtual task write(
    output uvm_status_e status, input uvm_reg_data_t value,
    input uvm_path_e path = UVM_DEFAULT_PATH, input uvm_reg_map map = null,
    input uvm_sequence_base parent = null, input int prior = -1,
    input uvm_object extension = null, input string fname = "",
    input int lineno = 0
  );
    #(response_delay);
    status = UVM_IS_OK;
  endtask
endclass

// Catch only the diagnostic explicitly armed by a negative check. All other
// failures retain their normal action, including the whole-test watchdog.
class usb_expected_timeout_catcher extends uvm_report_catcher;
  `uvm_object_utils(usb_expected_timeout_catcher)

  string expected_id;
  string expected_message;
  int unsigned caught_count;
  realtime caught_at;

  function new(string name = "usb_expected_timeout_catcher");
    super.new(name);
  endfunction

  virtual function action_e catch();
    if (get_severity() == UVM_FATAL && expected_id != "" &&
        get_id() == expected_id && uvm_is_match(expected_message, get_message())) begin
      caught_count++;
      caught_at = $realtime;
      return CAUGHT;
    end
    return THROW;
  endfunction
endclass

// Utility-level tests reuse production helpers and validators. Synthetic RAL
// responses and completion events isolate watchdog semantics from USB traffic;
// usb_init and usb_dev_skip separately cover the real VIP/DUT integration.
class usb_utility_timeout_test extends usb_base_test;
  `uvm_component_utils(usb_utility_timeout_test)

  usb_base_seq device_sequence;
  usb_host_base_seq host_sequence;
  usb_delayed_reg delayed_reg;
  usb_expected_timeout_catcher timeout_catcher;
  uvm_sequencer #(svt_usb_transfer) stalled_sequencer;
  int unsigned checks;

  function new(string name = "usb_utility_timeout_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    stalled_sequencer = uvm_sequencer#(svt_usb_transfer)::type_id::create("stalled_sequencer", this);
  endfunction

  // Arm exactly one expected fatal; a missing or duplicate report fails.
  function void expect_timeout(string id, string message);
    timeout_catcher.expected_id = id;
    timeout_catcher.expected_message = message;
    timeout_catcher.caught_count = 0;
    timeout_catcher.caught_at = 0;
  endfunction

  // Check both the diagnostic and its exact time, then disarm the catcher.
  function void check_timeout(string label, realtime deadline);
    timeout_catcher.expected_id = "";
    if (timeout_catcher.caught_count != 1 || usb_time_ps(timeout_catcher.caught_at) != usb_time_ps(deadline)) begin
      `uvm_fatal("USB_UTILITY_TEST", $sformatf("%s: expected one timeout at %0t; count=%0d time=%0t", label, deadline, timeout_catcher.caught_count, timeout_catcher.caught_at))
    end
    checks++;
    `uvm_info("USB_UTILITY_TEST", $sformatf("Verified %s deadline at %0t", label, deadline), UVM_LOW)
  endfunction

  // Exercise normal access, boundary expiry, and responses after the budget.
  task check_access(bit is_write, realtime delay_value);
    logic [31:0] data;
    realtime started;
    bit expect_failure;

    delayed_reg.response_delay = delay_value;
    started = $realtime;
    expect_failure = delay_value >= env_cfg.transfer_timeout;
    `uvm_info("USB_UTILITY_TEST", $sformatf("Checking RAL %s delay=%0t budget=%0t", is_write ? "write" : "read", delay_value, env_cfg.transfer_timeout), UVM_LOW)
    if (expect_failure) expect_timeout("USB_RAL_TIMEOUT", "RAL * probe did not complete before *");
    if (is_write) device_sequence.ral_write32("probe", delayed_reg, 1);
    else device_sequence.ral_read32("probe", delayed_reg, data);
    if (expect_failure) begin
      check_timeout("RAL access", started + env_cfg.transfer_timeout);
      if (usb_time_ps($realtime) != usb_time_ps(started + env_cfg.transfer_timeout)) begin
        `uvm_fatal("USB_UTILITY_TEST", "RAL access returned after its deadline")
      end
    end else begin
      if (usb_time_ps($realtime) != usb_time_ps(started + delay_value) || (!is_write && data !== 32'd1)) begin
        `uvm_fatal("USB_UTILITY_TEST", "Before-deadline RAL access returned incorrect data or timing")
      end
      checks++;
    end
  endtask

  // The poll budget is shorter than the access budget. Also test pacing that
  // would otherwise sleep past expiry, and a clear-bit success.
  task check_poll(realtime delay_value, bit matching_value, bit want_set = 1);
    logic [31:0] data;
    realtime started;
    bit expect_failure;

    delayed_reg.response_delay = delay_value;
    delayed_reg.response_value = matching_value ? 32'(want_set) : 32'(!want_set);
    started = $realtime;
    expect_failure = !matching_value || delay_value >= 100ns;
    `uvm_info("USB_UTILITY_TEST", $sformatf("Checking poll delay=%0t matching=%0b want_set=%0b", delay_value, matching_value, want_set), UVM_LOW)
    if (expect_failure) expect_timeout("USB_EP", "probe was not satisfied within *");
    device_sequence.poll_csr_bits("probe", delayed_reg, 1, want_set, 100ns, data, 200ns);
    if (expect_failure) begin
      check_timeout("CSR poll", started + 100ns);
      if (usb_time_ps($realtime) != usb_time_ps(started + 100ns)) `uvm_fatal("USB_UTILITY_TEST", "Poll returned after its deadline")
    end else begin
      if (usb_time_ps($realtime) != usb_time_ps(started + delay_value) || data !== 32'(want_set)) begin
        `uvm_fatal("USB_UTILITY_TEST", "Before-deadline poll returned incorrect data or timing")
      end
      checks++;
    end
  endtask

  // Exercise the actual blocking UVM calls: no driver for grant starvation,
  // or a driver that accepts an item but never calls item_done.
  task check_submission_stall(bit stall_grant);
    svt_usb_transfer item;
    svt_usb_transfer driver_item;
    uvm_object completion;
    realtime started;
    bit submission_returned;

    item = svt_usb_transfer::type_id::create("stalled_item");
    `uvm_info("USB_UTILITY_TEST", $sformatf("Checking host submission stall at %s", stall_grant ? "start_item" : "finish_item"), UVM_LOW)
    expect_timeout("USB_HOST", "probe submission/completion did not finish before *");
    started = $realtime;
    host_sequence.begin_transfer_watch("probe", 100ns);
    fork
      begin
        fork
          begin
            host_sequence.start_item(item, -1, stalled_sequencer);
            host_sequence.finish_item(item);
            submission_returned = 1;
          end
          begin
            if (!stall_grant) stalled_sequencer.get_next_item(driver_item);
            wait (timeout_catcher.caught_count != 0);
          end
        join_any
        disable fork;
      end
    join
    check_timeout("Host submission", started + 100ns);
    if (submission_returned || (!stall_grant && driver_item !== item)) begin
      `uvm_fatal("USB_UTILITY_TEST", "Submission probe did not stall at the intended handshake")
    end
    host_sequence.end_transfer_watch(completion);
    if (completion !== null) `uvm_fatal("USB_UTILITY_TEST", "Expired host watch returned a completion")
    stalled_sequencer.stop_sequences();
  endtask

  // Synthetic events test exact expiry and early observation followed by
  // late submission return. They do not drive any DUT signals.
  task check_host_completion(realtime event_delay, realtime submission_delay);
    svt_usb_transfer item;
    uvm_object completion;
    realtime started;
    bit expect_failure;
    bit sibling_finished;

    item = svt_usb_transfer::type_id::create("observed_item");
    expect_failure = event_delay >= 100ns || submission_delay >= 100ns;
    `uvm_info("USB_UTILITY_TEST", $sformatf("Checking host event=%0t submission=%0t", event_delay, submission_delay), UVM_LOW)
    if (expect_failure) expect_timeout("USB_HOST", "probe submission/completion did not finish before *");
    started = $realtime;
    host_sequence.begin_transfer_watch("probe", 100ns);
    fork
      begin
        #(event_delay);
        env.host_agent.prot.NOTIFY_USB_TRANSFER_ENDED.trigger(item);
      end
      begin
        #(submission_delay);
        host_sequence.end_transfer_watch(completion);
      end
      begin
        #150ns;
        sibling_finished = 1;
      end
    join
    if (!sibling_finished) `uvm_fatal("USB_UTILITY_TEST", "Host watch killed unrelated activity")
    if (expect_failure) begin
      check_timeout("Host completion", started + 100ns);
      if (completion !== null) `uvm_fatal("USB_UTILITY_TEST", "Late host completion was accepted")
    end else begin
      if (completion !== item) `uvm_fatal("USB_UTILITY_TEST", "Before-deadline host completion was lost")
      checks++;
    end
  endtask

  // Every unexpected result bit must reject an otherwise valid completion.
  task check_bulk_results();
    usb_dev_skip_host_seq bulk_sequence;
    svt_usb_transfer item;
    string reason;

    `uvm_info("USB_UTILITY_TEST", "Checking bulk result mask rejection", UVM_LOW)
    bulk_sequence = usb_dev_skip_host_seq::type_id::create("bulk_validator");
    bulk_sequence.target_endpoint = env_cfg.get_endpoint(1, USB_DIRECTION_OUT);
    bulk_sequence.payload_byte_count = 16;
    item = svt_usb_transfer::type_id::create("bulk_completion");
    item.status = svt_sequence_item::ACCEPT;
    item.results_status = '0;
    item.xfer_type = svt_usb_transfer::BULK_OUT_TRANSFER;
    item.device_address = bulk_sequence.device_address;
    item.endpoint_number = 1;
    item.payload.byte_count = 16;
    if (!bulk_sequence.validate_completed_transfer(item, reason)) begin
      `uvm_fatal("USB_UTILITY_TEST", {"Valid bulk completion rejected: ", reason})
    end
    checks++;
    for (int index = 0; index < $bits(item.results_status); index++) begin
      item.results_status = '0;
      item.results_status[index] = 1'b1;
      if (bulk_sequence.validate_completed_transfer(item, reason) ||
          !uvm_is_match("results_status does not match*", reason)) begin
        `uvm_fatal("USB_UTILITY_TEST", $sformatf("Result bit %0d was not rejected for the expected reason: %s", index, reason))
      end
      checks++;
    end
  endtask

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    env.wait_for_reset();
    device_sequence = usb_base_seq::type_id::create("device_utilities");
    device_sequence.set_sequencer(env.virtual_sequencer);
    host_sequence = usb_host_base_seq::type_id::create("host_utilities");
    host_sequence.set_sequencer(env.host_agent.virt_sequencer);
    host_sequence.resolve_host_context();
    delayed_reg = usb_delayed_reg::type_id::create("delayed_reg");
    timeout_catcher = usb_expected_timeout_catcher::type_id::create("timeout_catcher");
    uvm_report_cb::add(null, timeout_catcher);

    env_cfg.transfer_timeout = 100ns;
    for (int is_write = 0; is_write <= 1; is_write++) begin
      check_access(1'(is_write), 99.999ns);
      check_access(1'(is_write), 100ns);
      check_access(1'(is_write), 1ms);
    end
    env_cfg.transfer_timeout = 1us;
    check_poll(99.999ns, 1);
    check_poll(99.999ns, 1, 0);
    check_poll(100ns, 1);
    check_poll(101ns, 1);
    check_poll(1ms, 1);
    check_poll(10ns, 0);

    check_submission_stall(1);
    check_submission_stall(0);
    check_host_completion(99.999ns, 0ns);
    check_host_completion(100ns, 0ns);
    check_host_completion(101ns, 0ns);
    check_host_completion(10ns, 110ns);
    check_host_completion(10ns, 20ns);
    check_bulk_results();

    uvm_report_cb::delete(null, timeout_catcher);
    scenario_completed = 1;
    `uvm_info("USB_UTILITY_TEST", $sformatf("Completed %0d utility checks; all expected timeouts and result rejections verified", checks), UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass
