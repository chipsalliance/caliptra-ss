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

// Corrupts one bulk OUT token CRC5 and checks DUT detection plus host retry.
class usb_bad_crc5_seq extends usb_base_seq;
  `uvm_object_utils(usb_bad_crc5_seq)

  localparam logic [3:0] ERROR_TOKEN_CRC = 4'h4;

  logic [31:0] buffer_offset = 32'h0000_0200;
  int unsigned payload_bytes = 64;
  logic [7:0] payload_base = 8'h60;
  time error_timeout = 500us;
  bit completed;

  function new(string name = "usb_bad_crc5_seq");
    super.new(name);
  endfunction

  // Wait for INFO.ERR_CODE to report the expected SIE error.
  task wait_for_error_code(logic [3:0] expected_error);
    uvm_reg_field error_field;
    logic [31:0] info_value;
    logic [3:0] observed_error;
    realtime deadline;

    error_field = p_sequencer.reg_model.combo.dev0_csr.INFO.ERR_CODE;
    observed_error = 4'h0;
    deadline = $realtime + error_timeout;
    `uvm_info("USB_BAD_CRC5", $sformatf("Waiting up to %0t for INFO.ERR_CODE=0x%0h", error_timeout, expected_error), UVM_LOW)
    while (observed_error !== expected_error && $realtime < deadline) begin
      ral_read32("INFO", p_sequencer.reg_model.combo.dev0_csr.INFO, info_value);
      observed_error = 4'((info_value & ral_field_mask(error_field)) >> error_field.get_lsb_pos());
      if (observed_error !== expected_error) begin
        #500ns;
      end
    end
    if (observed_error !== expected_error) begin
      `uvm_fatal("USB_BAD_CRC5", $sformatf("INFO.ERR_CODE did not reach 0x%0h within %0t; last=0x%0h", expected_error, error_timeout, observed_error))
    end
    `uvm_info("USB_BAD_CRC5", $sformatf("DUT reported INFO.ERR_CODE=0x%0h for bad token CRC5", observed_error), UVM_LOW)
  endtask

  // Verify retry completion and the final received payload.
  task verify_transfer(usb_endpoint_cfg endpoint);
    usb_ep_entry_t entry;
    logic [31:0] observed_word;
    logic [31:0] expected_word;

    read_endpoint_entry(endpoint, entry);
    if (entry.active !== 1'b0 || entry.nbytes !== 0) begin
      `uvm_fatal("USB_BAD_CRC5", $sformatf("Bulk OUT did not retire after CRC5 retry: %s", describe_entry(entry)))
    end
    for (int unsigned offset = 0; offset < payload_bytes; offset += 4) begin
      expected_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        expected_word[8*lane +: 8] = payload_base + offset + lane;
      end
      read32(USB_DEV0_SRAM, buffer_offset + offset, observed_word);
      if (observed_word !== expected_word) begin
        `uvm_fatal(
          "USB_BAD_CRC5",
          $sformatf("Retried payload mismatch at offset %0d: data=0x%08h expected=0x%08h", offset, observed_word, expected_word)
        )
      end
    end
  endtask

  // Enumerate, inject one token CRC5 error, and verify transparent recovery.
  virtual task body();
    usb_init_seq init_sequence;
    usb_bulk_out_host_seq host_sequence;
    usb_endpoint_cfg endpoint;
    usb_ep_entry_t entry;
    svt_usb_agent host_agent;
    svt_configuration base_usb_cfg;
    svt_usb_configuration usb_cfg;
    svt_usb_protocol_20_host_tx_packet_crc5_error crc5_callback;

    completed = 1'b0;
    `uvm_info("USB_BAD_CRC5", "Starting bad token CRC5 scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_BAD_CRC5", "Enumeration did not complete")
    end
    if (!$cast(host_agent, p_sequencer.host_sequencer.get_parent())) begin
      `uvm_fatal("USB_BAD_CRC5", "Unable to resolve the SVT host agent")
    end
    p_sequencer.host_sequencer.get_cfg(base_usb_cfg);
    if (!$cast(usb_cfg, base_usb_cfg)) begin
      `uvm_fatal("USB_BAD_CRC5", "Unable to resolve the SVT USB configuration")
    end

    endpoint = get_endpoint(1, USB_DIRECTION_OUT);
    check_buffer_clear_of_endpoint_list("Bad CRC5", buffer_offset, payload_bytes);
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
    host_sequence.transfer_label = "Bulk OUT with first-token CRC5 error";

    svt_usb_protocol_20_host_tx_packet_crc5_error::packet_count = 0;
    crc5_callback = svt_usb_protocol_20_host_tx_packet_crc5_error::type_id::create("crc5_callback");
    usb_cfg.disable_tend_to_end_delay_check_for_expected_timeout = 1'b1;
    host_agent.reconfigure(usb_cfg);
    uvm_callbacks#(svt_usb_protocol, svt_usb_protocol_callback)::add(host_agent.prot, crc5_callback);
    `uvm_info("USB_BAD_CRC5", "Registered one-shot host token CRC5 corruption callback", UVM_LOW)
    fork
      begin
        host_sequence.start(p_sequencer.host_sequencer);
        if (!host_sequence.completed) begin
          `uvm_fatal("USB_BAD_CRC5", "Bulk OUT host sequence returned incomplete")
        end
      end
      begin
        wait_for_error_code(ERROR_TOKEN_CRC);
      end
    join
    uvm_callbacks#(svt_usb_protocol, svt_usb_protocol_callback)::delete(host_agent.prot, crc5_callback);
    usb_cfg.disable_tend_to_end_delay_check_for_expected_timeout = 1'b0;
    host_agent.reconfigure(usb_cfg);

    if (svt_usb_protocol_20_host_tx_packet_crc5_error::packet_count == 0) begin
      `uvm_fatal("USB_BAD_CRC5", "The CRC5 corruption callback did not modify a token")
    end
    wait_for_endpoint_interrupt(endpoint, error_timeout);
    verify_transfer(endpoint);

    completed = 1'b1;
    `uvm_info("USB_BAD_CRC5", "Bad token CRC5 was detected and the retried bulk OUT completed with correct data", UVM_LOW)
  endtask
endclass
