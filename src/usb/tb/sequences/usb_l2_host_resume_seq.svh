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

// Checks DEV0 L2 status across host resume and verifies post-resume traffic.
class usb_l2_host_resume_seq extends usb_base_seq;
  `uvm_object_utils(usb_l2_host_resume_seq)

  logic [31:0] recovery_buffer_offset = 32'h0000_0200;
  int unsigned recovery_bytes = 16;
  logic [7:0] recovery_payload_base = 8'hd0;
  time suspend_timeout = 750us;
  time status_poll_interval = 500ns;
  bit completed;

  function new(string name = "usb_l2_host_resume_seq");
    super.new(name);
  endfunction

  // Verify the endpoint and packet memory after post-resume bulk traffic.
  task verify_recovery_transfer(usb_endpoint_cfg endpoint);
    usb_ep_entry_t observed_entry;
    logic [31:0] observed_word;
    logic [31:0] expected_word;

    read_endpoint_entry(endpoint, observed_entry);
    if (observed_entry.nbytes !== 0 || observed_entry.active !== 1'b0) begin
      `uvm_fatal("USB_L2_SEQ", $sformatf("Post-resume endpoint did not retire cleanly: %s", describe_entry(observed_entry)))
    end
    for (int unsigned offset = 0; offset < recovery_bytes; offset += 4) begin
      expected_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        expected_word[8*lane +: 8] = recovery_payload_base + offset + lane;
      end
      read32(USB_DEV0_SRAM, recovery_buffer_offset + offset, observed_word);
      if (observed_word !== expected_word) begin
        `uvm_fatal("USB_L2_SEQ", $sformatf("Post-resume payload mismatch at offset 0x%03h: data=0x%08h expected=0x%08h", offset, observed_word, expected_word))
      end
    end
    `uvm_info("USB_L2_SEQ", $sformatf("Post-resume bulk OUT verified for all %0d bytes", recovery_bytes), UVM_LOW)
  endtask

  // Enumerate, check L2 entry/exit, then prove endpoint traffic recovers.
  virtual task body();
    usb_init_seq init_sequence;
    usb_l2_host_resume_host_seq suspend_host_sequence;
    usb_bulk_out_host_seq recovery_host_sequence;
    usb_endpoint_cfg recovery_endpoint;
    usb_ep_entry_t recovery_entry;
    uvm_event dut_suspend_observed;
    logic [31:0] device_command_status;
    logic [31:0] suspend_mask;

    completed = 1'b0;
    `uvm_info("USB_L2_SEQ", "Starting L2 host-resume scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_L2_SEQ", "Enumeration did not complete")
    end

    suspend_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.DSUS);
    dut_suspend_observed = new("dut_suspend_observed");
    suspend_host_sequence = usb_l2_host_resume_host_seq::type_id::create("suspend_host_sequence");
    suspend_host_sequence.dut_suspend_observed = dut_suspend_observed;
    suspend_host_sequence.link_state_timeout = suspend_timeout;

    fork
      begin
        suspend_host_sequence.start(p_sequencer.host_sequencer);
        if (!suspend_host_sequence.completed) begin
          `uvm_fatal("USB_L2_SEQ", "Host suspend/resume sequence returned incomplete")
        end
      end
      begin
        poll_csr_bits(
          "DEVCMDSTAT.DSUS assertion",
          p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT,
          suspend_mask,
          1'b1,
          suspend_timeout,
          device_command_status,
          status_poll_interval
        );
        `uvm_info("USB_L2_SEQ", $sformatf("DUT entered L2 suspend: DEVCMDSTAT=0x%08h", device_command_status), UVM_LOW)
        dut_suspend_observed.trigger();
        poll_csr_bits(
          "DEVCMDSTAT.DSUS deassertion",
          p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT,
          suspend_mask,
          1'b0,
          suspend_timeout,
          device_command_status,
          status_poll_interval
        );
        `uvm_info("USB_L2_SEQ", $sformatf("DUT left L2 suspend after host resume: DEVCMDSTAT=0x%08h", device_command_status), UVM_LOW)
      end
    join

    recovery_endpoint = get_endpoint(1, USB_DIRECTION_OUT);
    check_buffer_clear_of_endpoint_list("L2 recovery", recovery_buffer_offset, recovery_bytes);
    enable_endpoint_interrupt(recovery_endpoint);
    clear_endpoint_interrupt(recovery_endpoint);
    fill_endpoint_buffer(recovery_buffer_offset, recovery_bytes, 32'heeee_eeee);
    arm_endpoint(recovery_endpoint, recovery_bytes, recovery_buffer_offset, recovery_entry);

    recovery_host_sequence = usb_bulk_out_host_seq::type_id::create("recovery_host_sequence");
    recovery_host_sequence.target_endpoint = recovery_endpoint;
    recovery_host_sequence.payload_byte_count = recovery_bytes;
    recovery_host_sequence.payload_base = recovery_payload_base;
    recovery_host_sequence.device_address = p_sequencer.cfg.device_address;
    recovery_host_sequence.transfer_label = "Post-L2 recovery bulk OUT";
    fork
      begin
        recovery_host_sequence.start(p_sequencer.host_sequencer);
        if (!recovery_host_sequence.completed) begin
          `uvm_fatal("USB_L2_SEQ", "Post-resume host sequence returned incomplete")
        end
      end
      begin
        wait_for_endpoint_interrupt(recovery_endpoint, suspend_timeout, status_poll_interval);
      end
    join
    verify_recovery_transfer(recovery_endpoint);

    completed = 1'b1;
    `uvm_info("USB_L2_SEQ", "L2 host-resume scenario completed with DUT status transitions and recovery traffic verified", UVM_LOW)
  endtask
endclass
