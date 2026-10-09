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

// Supplies a checked post-resume bulk transfer for low-power scenarios.
class usb_resume_recovery_seq extends usb_base_seq;
  logic [31:0] recovery_buffer_offset = 32'h0000_0200;
  int unsigned recovery_bytes = 16;
  logic [7:0] recovery_payload_base = 8'hd0;
  time recovery_timeout = 750us;
  time recovery_poll_interval = 500ns;

  function new(string name = "usb_resume_recovery_seq");
    super.new(name);
  endfunction

  // Verify endpoint retirement and every byte of the recovery payload.
  task verify_recovery_transfer(usb_endpoint_cfg endpoint, string scenario_label);
    usb_ep_entry_t observed_entry;
    logic [31:0] observed_word;
    logic [31:0] expected_word;

    read_endpoint_entry(endpoint, observed_entry);
    if (observed_entry.nbytes !== 0 || observed_entry.active !== 1'b0) begin
      `uvm_fatal("USB_RESUME_RECOVERY", $sformatf("%s endpoint did not retire cleanly: %s", scenario_label, describe_entry(observed_entry)))
    end
    for (int unsigned offset = 0; offset < recovery_bytes; offset += 4) begin
      expected_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        expected_word[8*lane +: 8] = recovery_payload_base + offset + lane;
      end
      read32(USB_DEV0_SRAM, recovery_buffer_offset + offset, observed_word);
      if (observed_word !== expected_word) begin
        `uvm_fatal(
          "USB_RESUME_RECOVERY",
          $sformatf(
            "%s payload mismatch at offset 0x%03h: data=0x%08h expected=0x%08h",
            scenario_label,
            offset,
            observed_word,
            expected_word
          )
        )
      end
    end
    `uvm_info("USB_RESUME_RECOVERY", $sformatf("%s verified for all %0d bytes", scenario_label, recovery_bytes), UVM_LOW)
  endtask

  // Arm EP1 OUT, send known data, and verify the post-resume datapath.
  task run_recovery_transfer(string scenario_label);
    usb_bulk_out_host_seq host_sequence;
    usb_endpoint_cfg endpoint;
    usb_ep_entry_t entry;

    endpoint = get_endpoint(1, USB_DIRECTION_OUT);
    check_buffer_clear_of_endpoint_list(scenario_label, recovery_buffer_offset, recovery_bytes);
    enable_endpoint_interrupt(endpoint);
    clear_endpoint_interrupt(endpoint);
    fill_endpoint_buffer(recovery_buffer_offset, recovery_bytes, 32'heeee_eeee);
    arm_endpoint(endpoint, recovery_bytes, recovery_buffer_offset, entry);

    host_sequence = usb_bulk_out_host_seq::type_id::create("recovery_host_sequence");
    host_sequence.target_endpoint = endpoint;
    host_sequence.payload_byte_count = recovery_bytes;
    host_sequence.payload_base = recovery_payload_base;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.transfer_label = scenario_label;
    fork
      begin
        host_sequence.start(p_sequencer.host_sequencer);
        if (!host_sequence.completed) begin
          `uvm_fatal("USB_RESUME_RECOVERY", $sformatf("%s host sequence returned incomplete", scenario_label))
        end
      end
      begin
        wait_for_endpoint_interrupt(endpoint, recovery_timeout, recovery_poll_interval);
      end
    join
    verify_recovery_transfer(endpoint, scenario_label);
  endtask
endclass
