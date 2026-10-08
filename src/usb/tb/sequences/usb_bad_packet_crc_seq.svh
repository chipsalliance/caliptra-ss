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

// Shared malformed-CRC stimulus, DUT status checking, retry, and payload check.
virtual class usb_bad_packet_crc_seq extends usb_base_seq;
  logic [31:0] buffer_offset = 32'h0000_0200;
  int unsigned payload_bytes = 64;
  logic [7:0] payload_base = 8'h60;
  time error_timeout = 500us;
  bit completed;

  function new(string name = "usb_bad_packet_crc_seq");
    super.new(name);
  endfunction

  pure virtual function logic [3:0] expected_error_code();
  pure virtual function string scenario_label();
  pure virtual task install_injection(svt_usb_agent host_agent);
  pure virtual task remove_injection(svt_usb_agent host_agent);
  pure virtual function int unsigned injected_packet_count();

  // Wait for INFO.ERR_CODE to report the expected SIE status.
  task wait_for_error_code(logic [3:0] expected_code);
    uvm_reg_field error_field;
    logic [31:0] info_value;
    logic [3:0] observed_code;
    realtime deadline;

    error_field = p_sequencer.reg_model.combo.dev0_csr.INFO.ERR_CODE;
    observed_code = 4'h0;
    deadline = $realtime + error_timeout;
    `uvm_info("USB_BAD_PACKET_CRC", $sformatf("Waiting up to %0t for INFO.ERR_CODE=0x%0h", error_timeout, expected_code), UVM_LOW)
    while (observed_code !== expected_code && $realtime < deadline) begin
      ral_read32("INFO", p_sequencer.reg_model.combo.dev0_csr.INFO, info_value);
      observed_code = 4'((info_value & ral_field_mask(error_field)) >> error_field.get_lsb_pos());
      if (observed_code !== expected_code) begin
        #500ns;
      end
    end
    if (observed_code !== expected_code) begin
      `uvm_fatal(
        "USB_BAD_PACKET_CRC",
        $sformatf("INFO.ERR_CODE did not reach 0x%0h within %0t; last=0x%0h", expected_code, error_timeout, observed_code)
      )
    end
    `uvm_info(
      "USB_BAD_PACKET_CRC",
      $sformatf("DUT reported INFO.ERR_CODE=0x%0h for %s", observed_code, scenario_label()),
      UVM_LOW
    )
  endtask

  // Verify retry completion and the final received payload.
  task verify_transfer(usb_endpoint_cfg endpoint);
    usb_ep_entry_t entry;
    logic [31:0] observed_word;
    logic [31:0] expected_word;

    read_endpoint_entry(endpoint, entry);
    if (entry.active !== 1'b0 || entry.nbytes !== 0) begin
      `uvm_fatal("USB_BAD_PACKET_CRC", $sformatf("Bulk OUT did not retire after %s retry: %s", scenario_label(), describe_entry(entry)))
    end
    for (int unsigned offset = 0; offset < payload_bytes; offset += 4) begin
      expected_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        expected_word[8*lane +: 8] = payload_base + offset + lane;
      end
      read32(USB_DEV0_SRAM, buffer_offset + offset, observed_word);
      if (observed_word !== expected_word) begin
        `uvm_fatal(
          "USB_BAD_PACKET_CRC",
          $sformatf("Retried payload mismatch at offset %0d: data=0x%08h expected=0x%08h", offset, observed_word, expected_word)
        )
      end
    end
  endtask

  // Enumerate, inject one malformed packet, and verify transparent recovery.
  virtual task body();
    usb_init_seq init_sequence;
    usb_bulk_out_host_seq host_sequence;
    usb_endpoint_cfg endpoint;
    usb_ep_entry_t entry;
    svt_usb_agent host_agent;
    svt_configuration base_usb_cfg;
    svt_usb_configuration usb_cfg;

    completed = 1'b0;
    `uvm_info("USB_BAD_PACKET_CRC", $sformatf("Starting %s scenario; running enumeration first", scenario_label()), UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_BAD_PACKET_CRC", "Enumeration did not complete")
    end
    if (!$cast(host_agent, p_sequencer.host_sequencer.get_parent())) begin
      `uvm_fatal("USB_BAD_PACKET_CRC", "Unable to resolve the SVT host agent")
    end
    p_sequencer.host_sequencer.get_cfg(base_usb_cfg);
    if (!$cast(usb_cfg, base_usb_cfg)) begin
      `uvm_fatal("USB_BAD_PACKET_CRC", "Unable to resolve the SVT USB configuration")
    end

    endpoint = get_endpoint(1, USB_DIRECTION_OUT);
    check_buffer_clear_of_endpoint_list(scenario_label(), buffer_offset, payload_bytes);
    fill_endpoint_buffer(buffer_offset, payload_bytes, 32'heeee_eeee);
    arm_endpoint(endpoint, payload_bytes, buffer_offset, entry);
    enable_endpoint_interrupt(endpoint);
    clear_endpoint_interrupt(endpoint);
    ral_write32("INFO", p_sequencer.reg_model.combo.dev0_csr.INFO, 32'h0);

    host_sequence = usb_bulk_out_host_seq::type_id::create("host_sequence");
    host_sequence.target_endpoint = endpoint;
    host_sequence.payload_byte_count = payload_bytes;
    host_sequence.payload_base = payload_base;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.bulk_transfer_timeout = error_timeout;
    host_sequence.transfer_label = {"Bulk OUT with ", scenario_label()};

    usb_cfg.disable_tend_to_end_delay_check_for_expected_timeout = 1'b1;
    host_agent.reconfigure(usb_cfg);
    install_injection(host_agent);
    `uvm_info("USB_BAD_PACKET_CRC", $sformatf("Registered one-shot host injection for %s", scenario_label()), UVM_LOW)
    fork
      begin
        host_sequence.start(p_sequencer.host_sequencer);
        if (!host_sequence.completed) begin
          `uvm_fatal("USB_BAD_PACKET_CRC", "Bulk OUT host sequence returned incomplete")
        end
      end
      begin
        wait_for_error_code(expected_error_code());
      end
    join
    remove_injection(host_agent);
    usb_cfg.disable_tend_to_end_delay_check_for_expected_timeout = 1'b0;
    host_agent.reconfigure(usb_cfg);

    if (injected_packet_count() == 0) begin
      `uvm_fatal("USB_BAD_PACKET_CRC", $sformatf("The %s injection did not modify a packet", scenario_label()))
    end
    wait_for_endpoint_interrupt(endpoint, error_timeout);
    verify_transfer(endpoint);

    completed = 1'b1;
    `uvm_info(
      "USB_BAD_PACKET_CRC",
      $sformatf("%s was detected and the retried bulk OUT completed with correct data", scenario_label()),
      UVM_LOW
    )
  endtask
endclass
