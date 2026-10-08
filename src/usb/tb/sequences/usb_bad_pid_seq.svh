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

// Injects an invalid PID complement on UTMI and checks ERROR_PID_ENCODING.
class usb_bad_pid_seq extends usb_resume_recovery_seq;
  `uvm_object_utils(usb_bad_pid_seq)

  localparam logic [3:0] ERROR_PID_ENCODING = 4'h1;
  localparam logic [7:0] BAD_OUT_PID = 8'he0;

  time status_timeout = 500us;
  bit completed;

  function new(string name = "usb_bad_pid_seq");
    super.new(name);
    recovery_payload_base = 8'hb0;
  endfunction

  // Override the normal UTMI receive path for one malformed PID byte.
  task inject_bad_pid();
    if (p_sequencer.ctrl_vif == null || p_sequencer.usb_20_mac_if == null) begin
      `uvm_fatal("USB_BAD_PID", "Raw UTMI injection requires control and USB virtual interfaces")
    end

    wait (p_sequencer.usb_20_mac_if.utmi_dut_mac_if.RXActive === 1'b0);
    @(posedge p_sequencer.usb_20_mac_if.utmi_dut_mac_if.CLK);
    p_sequencer.ctrl_vif.raw_utmi_inject_enable <= 1'b1;
    p_sequencer.ctrl_vif.raw_utmi_rxactive <= 1'b1;
    p_sequencer.ctrl_vif.raw_utmi_rxvalid <= 1'b1;
    p_sequencer.ctrl_vif.raw_utmi_rxerror <= 1'b0;
    p_sequencer.ctrl_vif.raw_utmi_rxdata <= BAD_OUT_PID;
    repeat (2) @(posedge p_sequencer.usb_20_mac_if.utmi_dut_mac_if.CLK);
    p_sequencer.ctrl_vif.raw_utmi_rxvalid <= 1'b0;
    p_sequencer.ctrl_vif.raw_utmi_rxactive <= 1'b0;
    @(posedge p_sequencer.usb_20_mac_if.utmi_dut_mac_if.CLK);
    p_sequencer.ctrl_vif.raw_utmi_inject_enable <= 1'b0;
    `uvm_info("USB_BAD_PID", $sformatf("Injected malformed OUT PID byte 0x%02h at the UTMI receive boundary", BAD_OUT_PID), UVM_LOW)
  endtask

  // Enumerate, inject bad PID encoding, and prove normal traffic recovers.
  virtual task body();
    usb_init_seq init_sequence;

    completed = 1'b0;
    `uvm_info("USB_BAD_PID", "Starting bad PID encoding scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_BAD_PID", "Enumeration did not complete")
    end

    ral_write32("INFO", p_sequencer.reg_model.combo.dev0_csr.INFO, 32'h0);
    inject_bad_pid();
    wait_for_sie_error_code(ERROR_PID_ENCODING, status_timeout, "bad PID encoding");

    recovery_timeout = status_timeout;
    run_recovery_transfer("Post-bad-PID recovery bulk OUT");

    completed = 1'b1;
    `uvm_info("USB_BAD_PID", "Bad PID encoding was detected and normal bulk OUT traffic recovered", UVM_LOW)
  endtask
endclass
