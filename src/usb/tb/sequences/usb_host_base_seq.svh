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
// Generic mechanics shared by every host-side USB sequence in this bench.
//
// This class owns only transfer-independent plumbing: resolving the SVT host
// agent and configuration from the virtual sequencer, waiting for USB 2.0 link
// enablement, and the submit/observe/timeout handshake around
// NOTIFY_USB_TRANSFER_ENDED. Deciding what to send and whether a completion is
// correct stays in the derived scenario sequence.
//
// Completion observation is split into two calls because the observer must be
// armed before the transfer is submitted, while the transfer's construction and
// randomization are scenario-specific and cannot be hidden behind a single
// utility task:
//
//   resolve_host_context();
//   begin_transfer_watch("label", timeout);
//   start_item(...); ... randomize ... ; finish_item(...);
//   end_transfer_watch(completed_object);
//
// begin_transfer_watch() returns only after its observer is blocked on the
// event, so a completion that arrives immediately after finish_item() cannot
// be missed. The watchdog remains active through submission and completion;
// events and finish_item returning do not restart the budget.
//
// Event correlation: the SVT protocol layer reports transfer completions as a
// stream, and the ended event does not identify which submitted item it
// belongs to. With a single transfer in flight, accepting the first ended event
// is correct. check_transfer_correlation() records whether the reported object
// is the submitted item so this assumption is visible in the log rather than
// silent, and require_transfer_handle_match promotes a mismatch to a failure
// for any future scenario that keeps more than one transfer outstanding.
class usb_host_base_seq extends uvm_sequence;
  `uvm_object_utils(usb_host_base_seq)
  `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

  // Resolved once by resolve_host_context() and reused by every transfer.
  svt_usb_agent host_agent;
  svt_usb_configuration usb_cfg;
  svt_usb_status shared_status;

  // Set by a scenario that keeps more than one transfer in flight and therefore
  // cannot accept the first ended event as its own.
  bit require_transfer_handle_match;

  // Published by the derived scenario only after every transfer it owns has
  // been validated; the parent device-side sequence consumes it.
  bit completed;

  // Owned by the observer started in begin_transfer_watch(). The handle is kept
  // so end_transfer_watch() can retire exactly that process; a bare
  // "disable fork" there would run in the caller's process and would also kill
  // the SVT threads spawned while the transfer was being driven.
  protected uvm_object observed_completion;
  protected bit observed_transfer_ended;
  protected process observer_process;
  protected process watchdog_process;
  protected bit watch_active;
  protected bit watch_expired;
  protected string watch_label;
  protected time watch_timeout;
  protected realtime watch_deadline;

  function new(string name = "usb_host_base_seq");
    super.new(name);
  endfunction

  // Report identifier so each derived sequence keeps its own message prefix
  // while sharing these diagnostics.
  virtual function string report_id();
    return "USB_HOST";
  endfunction

  // Resolve the SVT objects usb_env published for the host agent. Every
  // failure is fatal here rather than producing a null dereference deeper in
  // a scenario.
  task resolve_host_context(bit require_shared_status = 1'b0);
    svt_configuration base_cfg;

    if (p_sequencer == null || !$cast(host_agent, p_sequencer.get_parent())) begin
      `uvm_fatal(report_id(), "Sequence must run on the SVT host_agent virtual sequencer")
    end
    p_sequencer.get_cfg(base_cfg);
    if (!$cast(usb_cfg, base_cfg)) begin
      `uvm_fatal(report_id(), "SVT USB configuration is unavailable")
    end
    if (require_shared_status) begin
      shared_status = p_sequencer.get_shared_status(this);
      if (shared_status === null) begin
        `uvm_fatal(report_id(), "SVT shared status is unavailable")
      end
    end
  endtask

  // Block until the USB 2.0 link is ENABLED, which must happen before SOF
  // generation or any endpoint traffic can start.
  task wait_for_link_enabled(time timeout);
    bit link_enabled;

    if (shared_status === null) begin
      `uvm_fatal(report_id(), "wait_for_link_enabled() requires the shared status; call resolve_host_context(1) first")
    end
    link_enabled = 1'b0;
    `uvm_info(report_id(), "Waiting for the SVT USB 2.0 host link to reach ENABLED", UVM_LOW)
    fork
      begin
        wait (shared_status.link_usb_20_state === svt_usb_types::ENABLED);
        link_enabled = 1'b1;
      end
      begin
        #(timeout);
      end
    join_any
    disable fork;

    if (!link_enabled) begin
      `uvm_fatal(report_id(), $sformatf("USB link did not reach ENABLED within %0t; state=%p", timeout, shared_status.link_usb_20_state))
    end
    `uvm_info(report_id(), "SVT USB host link is ENABLED", UVM_LOW)
  endtask

  // Arm observation and the watchdog before submission can block. One budget
  // covers arbitration, driver acceptance, and the bus completion event.
  task begin_transfer_watch(string label, time timeout);
    if (host_agent == null) begin
      `uvm_fatal(report_id(), "begin_transfer_watch() requires the host agent; call resolve_host_context() first")
      return;
    end
    if (watch_active || timeout == 0) begin
      `uvm_fatal(report_id(), "Transfer watch requires no active watch and a nonzero timeout")
      return;
    end
    watch_active = 1'b1;
    watch_expired = 1'b0;
    watch_label = label;
    watch_timeout = timeout;
    watch_deadline = $realtime + timeout;
    observed_transfer_ended = 1'b0;
    observed_completion = null;
    observer_process = null;
    watchdog_process = null;
    `uvm_info(report_id(), $sformatf("Watching %s submission and completion; timeout=%0t", label, timeout), UVM_LOW)
    fork
      begin
        observer_process = process::self();
        host_agent.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger_data(observed_completion);
        observed_transfer_ended = 1'b1;
      end
      begin
        watchdog_process = process::self();
        #(timeout);
        watch_expired = 1'b1;
        `uvm_fatal(report_id(), $sformatf("%s submission/completion did not finish before %0t", watch_label, watch_timeout))
      end
    join_none
    // Let the observer reach its blocking wait before the caller submits.
    #0;
  endtask

  // Complete the watch after submission returns. Retire only our processes,
  // leaving SVT activity untouched. Completion at the deadline is too late.
  task end_transfer_watch(output uvm_object completed_object);
    completed_object = null;
    if (!watch_active) begin
      `uvm_fatal(report_id(), "end_transfer_watch() requires an active watch")
      return;
    end
    wait (observed_transfer_ended || watch_expired);

    if (observer_process != null && observer_process.status() != process::FINISHED) begin
      observer_process.kill();
    end
    if (watchdog_process != null && watchdog_process.status() != process::FINISHED) begin
      watchdog_process.kill();
    end
    observer_process = null;
    watchdog_process = null;
    watch_active = 1'b0;

    // If a report catcher suppresses the watchdog fatal, never return its
    // completion as a success or issue the same timeout diagnostic twice.
    if (watch_expired) return;
    if (usb_time_ps($realtime) >= usb_time_ps(watch_deadline)) begin
      `uvm_fatal(report_id(), $sformatf("%s submission/completion did not finish before %0t", watch_label, watch_timeout))
      return;
    end
    completed_object = observed_completion;
    `uvm_info(report_id(), $sformatf("%s submission and completion finished within %0t", watch_label, watch_timeout), UVM_LOW)
  endtask

  // Convert an ended-event object into a transfer, rejecting null or foreign
  // objects before any transfer field is read. Scenario-specific validation
  // starts from the returned transfer.
  function bit cast_completed_transfer(uvm_object completed_object, output svt_usb_transfer transfer, output string failure_reason);
    failure_reason = "";
    transfer = null;
    if (completed_object === null) begin
      failure_reason = "completion object is null";
      return 1'b0;
    end
    if (!$cast(transfer, completed_object) || transfer === null) begin
      failure_reason = $sformatf("completion object type %s is not svt_usb_transfer", completed_object.get_type_name());
      return 1'b0;
    end
    return 1'b1;
  endfunction

  // Record whether the reported completion is the item that was submitted.
  // Default behavior only logs, preserving first-event-wins for the
  // single-outstanding scenarios this bench runs today.
  function void check_transfer_correlation(string label, svt_usb_transfer submitted_transfer, uvm_object completed_object);
    bit handles_match;

    handles_match = (submitted_transfer !== null) && (completed_object === submitted_transfer);
    if (handles_match) begin
      `uvm_info(report_id(), $sformatf("%s completion is the submitted item", label), UVM_HIGH)
      return;
    end
    if (require_transfer_handle_match) begin
      `uvm_fatal(report_id(), $sformatf("%s completion is not the submitted item; a correlated completion was required", label))
    end
    `uvm_info(report_id(), $sformatf("%s completion is a distinct object from the submitted item; accepted because only one transfer was outstanding", label), UVM_HIGH)
  endfunction
endclass
