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

// Injects an IN token with an invalid PID complement to an armed IN endpoint,
// verifies DUT INFO.ERR_CODE == ERROR_PID_ENCODING (4'h1) and non-consumption
// of the armed IN descriptor, and proves subsequent bulk OUT recovery traffic
// completes cleanly.
//
// Uses native PID_CHECK_ERROR injection (exception/class_svt_usb_packet_exception.html)
// and supported link/physical checking. Endpoint protocol checks are unsupported
// in this UTMI 4-stack topology and are not credited here.
// Explicit DUT error/descriptor checks establish rejection without consumption;
// EPSKIP returns ownership before cleanup, and the bulk helper checks recovery.
class usb_bad_pid_seq extends usb_resume_recovery_seq;
  `uvm_object_utils(usb_bad_pid_seq)

  localparam logic [3:0] ERROR_PID_ENCODING = 4'h1;
  localparam logic [31:0] READY_IN_BUFFER_OFFSET = 32'h0000_0240;

  time status_timeout = 500us;
  bit completed;

  function new(string name = "usb_bad_pid_seq");
    super.new(name);
    recovery_payload_base = 8'hb0;
  endfunction

  // USB 2.0 Section 8.1 requires the high PID nibble to complement the low.
  task inject_bad_pid();
    usb_bad_pid_packet_seq packet_sequence;

    packet_sequence = usb_bad_pid_packet_seq::type_id::create("bad_pid_packet");
    packet_sequence.device_address = p_sequencer.cfg.device_address;
    packet_sequence.endpoint_number = 4'd1;
    packet_sequence.start(p_sequencer.host_sequencer.usb_20_pkt_sequencer, this);
    `uvm_info("USB_BAD_PID", "Injected VIP PID_CHECK_ERROR on one IN token to armed EP1 IN", UVM_LOW)
  endtask

  // Enumerate, inject bad PID encoding against an armed IN endpoint, verify it
  // is ignored without consuming the IN descriptor, and prove traffic recovers.
  virtual task body();
    usb_init_seq init_sequence;
    usb_endpoint_cfg in_endpoint;
    usb_ep_entry_t in_entry;
    svt_usb_protocol_service_20_sof_off_sequence sof_off_sequence;
    svt_usb_protocol_service_20_sof_on_sequence sof_on_sequence;
    uvm_action saved_sequencer_warning_action;

    completed = 1'b0;
    `uvm_info("USB_BAD_PID", "Starting bad PID encoding scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_BAD_PID", "Enumeration did not complete")
    end

    in_endpoint = get_endpoint(1, USB_DIRECTION_IN);
    check_buffer_clear_of_endpoint_list("Bad-PID ready IN", READY_IN_BUFFER_OFFSET, recovery_bytes);
    fill_endpoint_buffer(READY_IN_BUFFER_OFFSET, recovery_bytes, 32'h5a5a_5a5a);
    arm_endpoint(in_endpoint, recovery_bytes, READY_IN_BUFFER_OFFSET, in_entry);

    ral_write32("INFO", p_sequencer.reg_model.combo.dev0_csr.INFO, 32'h0);
    saved_sequencer_warning_action =
        p_sequencer.host_sequencer.prot_service_sequencer.get_report_action(UVM_WARNING, "Sequencer");
    p_sequencer.host_sequencer.prot_service_sequencer.set_report_severity_id_action(
        UVM_WARNING, "Sequencer", UVM_NO_ACTION);
    sof_off_sequence =
        svt_usb_protocol_service_20_sof_off_sequence::type_id::create(
            "sof_off_sequence");
    sof_off_sequence.start(
        p_sequencer.host_sequencer.prot_service_sequencer);
    // Let any already-started SOF finish before injecting the malformed-PID token.
    #1us;
    inject_bad_pid();
    wait_for_sie_error_code(ERROR_PID_ENCODING, status_timeout, "bad PID encoding");
    // Allow more than one HS inter-packet turnaround window before checking
    // that the armed IN descriptor was not consumed by the malformed IN token.
    #1us;
    read_endpoint_entry(in_endpoint, in_entry);
    if (in_entry.active !== 1'b1 ||
        in_entry.nbytes !== recovery_bytes ||
        entry_buffer_byte_offset(in_entry) !== READY_IN_BUFFER_OFFSET) begin
      `uvm_fatal(
        "USB_BAD_PID",
        $sformatf("Malformed-PID IN token modified armed EP1 IN descriptor: %s", describe_entry(in_entry))
      )
    end
    // Programmers Guide 4.2 forbids rewriting an Active command/status word.
    `uvm_info("USB_BAD_PID", "Malformed PID left the IN descriptor owned; requesting EPSKIP before cleanup", UVM_LOW)
    request_endpoint_skip(in_endpoint);
    wait_for_endpoint_skip_clear(in_endpoint, status_timeout);
    in_entry.active = 1'b0;
    check_endpoint_entry_writeback(in_endpoint, in_entry, "Bad-PID cleanup skip altered more than Active");
    `uvm_info("USB_BAD_PID",
              $sformatf("EPSKIP returned IN ownership with residual/pointer preserved: %s", describe_entry(in_entry)), UVM_LOW)
    clear_endpoint_interrupt(in_endpoint);
    write_endpoint_entry(in_endpoint, '0);
    check_endpoint_entry_writeback(in_endpoint, '0, "Bad-PID cleanup did not clear the retired IN descriptor");
    `uvm_info("USB_BAD_PID", "Bad-PID IN cleanup verified: skip retired ownership and descriptor cleared", UVM_LOW)
    sof_on_sequence =
        svt_usb_protocol_service_20_sof_on_sequence::type_id::create(
            "sof_on_sequence");
    sof_on_sequence.start(
        p_sequencer.host_sequencer.prot_service_sequencer);
    p_sequencer.host_sequencer.prot_service_sequencer.set_report_severity_id_action(
        UVM_WARNING, "Sequencer", saved_sequencer_warning_action);

    recovery_timeout = status_timeout;
    run_recovery_transfer("Post-bad-PID recovery bulk OUT");

    completed = 1'b1;
    `uvm_info("USB_BAD_PID", "Bad PID encoding was detected and normal bulk OUT traffic recovered", UVM_LOW)
  endtask
endclass
