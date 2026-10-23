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

// Sends one SVT USB 2.0 packet with an intentional PID_CHECK_ERROR exception
// (transaction/class_svt_usb_packet_exception.html) on usb_20_pkt_sequencer.
class usb_bad_pid_packet_seq extends svt_usb_packet_base_sequence;
  `uvm_object_utils(usb_bad_pid_packet_seq)

  bit [6:0] device_address = USB_DEFAULT_DEVICE_ADDRESS;
  bit [3:0] endpoint_number = 4'd1;

  function new(string name = "usb_bad_pid_packet_seq");
    super.new(name);
  endfunction

  virtual task body();
    svt_usb_packet packet;
    svt_usb_packet_exception pid_exception;

    packet = new_item("bad_pid_out_token");
    packet.speed = svt_usb_types::HS;
    packet.payload = new("packet_payload");
    packet.payload_offset = 0;
    start_item(packet);
    if (!packet.randomize() with {
          pid_type == svt_usb_packet::TOKEN;
          pid_name == svt_usb_packet::OUT;
          device_address == local::device_address;
          ept_num == local::endpoint_number;
          payload.byte_count == 0;
        }) begin
      `uvm_fatal("USB_BAD_PID_PKT", "Failed to randomize bad-PID OUT token packet")
    end
    pid_exception = new("bad_pid_check");
    pid_exception.cfg = packet.cfg;
    pid_exception.xact = packet;
    pid_exception.error_group = svt_usb_packet_exception::RANDOM_ERROR_GROUP;
    pid_exception.error_kind = svt_usb_packet_exception::PID_CHECK_ERROR;
    pid_exception.mask_or_value = 32'h1;
    pid_exception.no_exception = 1'b0;
    pid_exception.recognized = 1'b0;
    if (packet.exception_list == null) begin
      packet.exception_list = new("packet_exceptions");
    end
    packet.exception_list.add_exception(pid_exception);
    finish_item(packet);
    if (!packet.end_is_on()) begin
      packet.wait_end();
    end
  endtask
endclass

// Injects an invalid PID complement through VIP and checks ERROR_PID_ENCODING.
//
// Relies on the Synopsys SVT USB VIP's built-in svt_usb_packet_exception
// (PID_CHECK_ERROR in transaction/class_svt_usb_packet_exception.html) and
// built-in protocol/link checks on the subsequent recovery bulk OUT transfer
// (enabled by default via register_default_chks = 1, enable_default_chks = 1 in
// protocolChecks.html, coverage/class_svt_usb_protocol_ep_sc.html, and
// coverage/class_svt_usb_link_20_sc.html):
//   - svt_usb_link_20_sc:
//     * unexpected_response_check: Verifies the device remains silent when a
//       packet with an invalid PID check field is received.
//   - svt_usb_protocol_ep_sc:
//     * packet_error_check, data_toggle_check, valid_device_response_check on
//       the post-error bulk OUT recovery transfer.
class usb_bad_pid_seq extends usb_resume_recovery_seq;
  `uvm_object_utils(usb_bad_pid_seq)

  localparam logic [3:0] ERROR_PID_ENCODING = 4'h1;

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
    `uvm_info("USB_BAD_PID", "Injected VIP PID_CHECK_ERROR on one OUT token", UVM_LOW)
  endtask

  // Enumerate, inject bad PID encoding, and prove normal traffic recovers.
  virtual task body();
    usb_init_seq init_sequence;
    svt_usb_protocol_service_20_sof_off_sequence sof_off_sequence;
    svt_usb_protocol_service_20_sof_on_sequence sof_on_sequence;

    completed = 1'b0;
    `uvm_info("USB_BAD_PID", "Starting bad PID encoding scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_BAD_PID", "Enumeration did not complete")
    end

    ral_write32("INFO", p_sequencer.reg_model.combo.dev0_csr.INFO, 32'h0);
    sof_off_sequence =
        svt_usb_protocol_service_20_sof_off_sequence::type_id::create(
            "sof_off_sequence");
    sof_off_sequence.start(
        p_sequencer.host_sequencer.prot_service_sequencer);
    inject_bad_pid();
    wait_for_sie_error_code(ERROR_PID_ENCODING, status_timeout, "bad PID encoding");
    sof_on_sequence =
        svt_usb_protocol_service_20_sof_on_sequence::type_id::create(
            "sof_on_sequence");
    sof_on_sequence.start(
        p_sequencer.host_sequencer.prot_service_sequencer);

    recovery_timeout = status_timeout;
    run_recovery_transfer("Post-bad-PID recovery bulk OUT");

    completed = 1'b1;
    `uvm_info("USB_BAD_PID", "Bad PID encoding was detected and normal bulk OUT traffic recovered", UVM_LOW)
  endtask
endclass
