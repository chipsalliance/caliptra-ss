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

// Injects an invalid PID complement through VIP and checks ERROR_PID_ENCODING.
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
    usb_vip_packet_seq packet_sequence;

    packet_sequence = usb_vip_packet_seq::type_id::create("bad_pid_packet");
    packet_sequence.packet_pid = svt_usb_packet::OUT;
    packet_sequence.device_address = p_sequencer.cfg.device_address;
    packet_sequence.endpoint_number = 1;
    packet_sequence.corrupt_pid_check = 1'b1;
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
