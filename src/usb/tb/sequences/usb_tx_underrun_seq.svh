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

// Starves bulk IN DMA and checks its corrupted CRC.
// Current RTL underflows the DMA FIFO pointer before reaching the CRC path;
// this sequence remains the acceptance test for that defect.
class usb_tx_underrun_seq extends usb_base_seq;
  `uvm_object_utils(usb_tx_underrun_seq)

  logic [31:0] buffer_offset = 32'h0000_0200;
  int unsigned payload_bytes = 512;
  logic [7:0] payload_base = 8'h40;
  time scenario_timeout = 500us;
  time starvation_duration = 5us;
  bit completed;

  function new(string name = "usb_tx_underrun_seq");
    super.new(name);
  endfunction

  // Calculate the transmitted USB CRC16 over a payload byte range.
  function logic [15:0] usb_crc16(byte unsigned bytes[$], int unsigned first, int unsigned count);
    logic [15:0] crc;
    byte unsigned data_byte;
    logic feedback;

    crc = 16'hffff;
    for (int unsigned byte_index = 0; byte_index < count; byte_index++) begin
      data_byte = bytes[first + byte_index];
      repeat (8) begin
        feedback = crc[0] ^ data_byte[0];
        crc >>= 1;
        if (feedback) crc ^= 16'ha001;
        data_byte >>= 1;
      end
    end
    return ~crc;
  endfunction

  // Require the first observed IN data packet to carry an intentionally bad CRC.
  function void check_corrupted_crc(usb_utmi_tx_packet packet);
    logic [15:0] expected_crc;
    logic [15:0] observed_crc;
    int unsigned payload_count;

    if (packet == null || packet.bytes.size() < 3) begin
      `uvm_fatal("USB_TX_UNDERRUN", "Underrun observation did not contain a complete DATA PID and CRC16")
      return;
    end
    if (packet.bytes[0] !== 8'hc3 && packet.bytes[0] !== 8'h4b) begin
      `uvm_fatal("USB_TX_UNDERRUN", $sformatf("Underrun packet PID is 0x%02h, expected DATA0 or DATA1", packet.bytes[0]))
    end
    payload_count = packet.bytes.size() - 3;
    expected_crc = usb_crc16(packet.bytes, 1, payload_count);
    observed_crc = {packet.bytes[packet.bytes.size() - 1], packet.bytes[packet.bytes.size() - 2]};
    if (observed_crc === expected_crc) begin
      `uvm_fatal(
        "USB_TX_UNDERRUN",
        $sformatf("Underrun packet CRC16 0x%04h is valid for its %0d payload bytes", observed_crc, payload_count)
      )
    end
    `uvm_info(
      "USB_TX_UNDERRUN",
      $sformatf("Observed corrupted CRC16 after %0d transmitted payload bytes: actual=0x%04h valid=0x%04h", payload_count, observed_crc, expected_crc),
      UVM_LOW
    )
  endfunction

  // Slow the DMA clock after transmission starts so its prefetch buffer drains.
  task run_dma_starvation(uvm_event tx_data_progress_event);
    tx_data_progress_event.wait_ptrigger();
    `uvm_info(
      "USB_TX_UNDERRUN",
      $sformatf("Observed 16 transmitted data bytes; slowing the DMA clock for %0t", starvation_duration),
      UVM_LOW
    )
    p_sequencer.ctrl_vif.slow_bus_clock <= 1'b1;
    #(starvation_duration);
    p_sequencer.ctrl_vif.slow_bus_clock <= 1'b0;
    `uvm_info("USB_TX_UNDERRUN", "Restored the normal DMA clock rate", UVM_LOW)
  endtask

  // Enumerate, force one underrun, check the bad CRC, and allow a valid retry.
  virtual task body();
    usb_init_seq init_sequence;
    usb_bulk_in_host_seq host_sequence;
    usb_bulk_in_host_seq retry_sequence;
    usb_endpoint_cfg endpoint;
    usb_ep_entry_t entry;
    uvm_event tx_data_progress_event;
    uvm_event tx_data_packet_event;
    uvm_object observed_object;
    usb_utmi_tx_packet observed_packet;
    svt_usb_agent host_agent;
    svt_configuration base_usb_cfg;
    svt_usb_configuration usb_cfg;

    completed = 1'b0;
    `uvm_info("USB_TX_UNDERRUN", "Starting bulk IN underrun scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_TX_UNDERRUN", "Enumeration did not complete")
    end
    if (!$cast(host_agent, p_sequencer.host_sequencer.get_parent())) begin
      `uvm_fatal("USB_TX_UNDERRUN", "Unable to resolve the SVT host agent")
    end
    p_sequencer.host_sequencer.get_cfg(base_usb_cfg);
    if (!$cast(usb_cfg, base_usb_cfg)) begin
      `uvm_fatal("USB_TX_UNDERRUN", "Unable to resolve the SVT USB configuration")
    end

    endpoint = get_endpoint(1, USB_DIRECTION_IN);
    check_buffer_clear_of_endpoint_list("Bulk IN underrun", buffer_offset, payload_bytes);
    for (int unsigned offset = 0; offset < payload_bytes; offset += 4) begin
      logic [31:0] data_word;

      for (int unsigned lane = 0; lane < 4; lane++) begin
        data_word[8*lane +: 8] = payload_base + offset + lane;
      end
      write32(USB_DEV0_SRAM, buffer_offset + offset, data_word);
    end
    arm_endpoint(endpoint, payload_bytes, buffer_offset, entry);
    enable_endpoint_interrupt(endpoint);
    clear_endpoint_interrupt(endpoint);
    ral_write32("INFO", p_sequencer.reg_model.combo.dev0_csr.INFO, 32'h0);

    tx_data_progress_event = uvm_event_pool::get_global(USB_UTMI_TX_DATA_PROGRESS_EVENT);
    tx_data_packet_event = uvm_event_pool::get_global(USB_UTMI_TX_DATA_PACKET_EVENT);
    tx_data_progress_event.reset();
    tx_data_packet_event.reset();
    host_sequence = usb_bulk_in_host_seq::type_id::create("host_sequence");
    host_sequence.target_endpoint = endpoint;
    host_sequence.payload_byte_count = payload_bytes;
    host_sequence.payload_base = payload_base;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.bulk_transfer_timeout = scenario_timeout;
    host_sequence.transfer_label = "Bulk IN with DMA underrun";
    host_sequence.expect_non_success = 1'b1;

    usb_cfg.disable_tend_to_end_delay_check_for_expected_timeout = 1'b1;
    host_agent.reconfigure(usb_cfg);
    fork
      begin
        host_sequence.start(p_sequencer.host_sequencer);
        if (!host_sequence.completed) begin
          `uvm_fatal("USB_TX_UNDERRUN", "Bulk IN host sequence returned incomplete")
        end
      end
      begin
        run_dma_starvation(tx_data_progress_event);
      end
      begin
        tx_data_packet_event.wait_trigger_data(observed_object);
      end
    join
    usb_cfg.disable_tend_to_end_delay_check_for_expected_timeout = 1'b0;
    host_agent.reconfigure(usb_cfg);

    if (!$cast(observed_packet, observed_object)) begin
      `uvm_fatal("USB_TX_UNDERRUN", "UTMI TX event carried an unexpected object type")
    end
    check_corrupted_crc(observed_packet);
    read_endpoint_entry(endpoint, entry);
    if (entry.active !== 1'b1 || entry.nbytes !== payload_bytes) begin
      `uvm_fatal("USB_TX_UNDERRUN", $sformatf("Bulk IN descriptor changed after failed packet: %s", describe_entry(entry)))
    end

    retry_sequence = usb_bulk_in_host_seq::type_id::create("retry_sequence");
    retry_sequence.target_endpoint = endpoint;
    retry_sequence.payload_byte_count = payload_bytes;
    retry_sequence.payload_base = payload_base;
    retry_sequence.device_address = p_sequencer.cfg.device_address;
    retry_sequence.bulk_transfer_timeout = scenario_timeout;
    retry_sequence.transfer_label = "Bulk IN retry after DMA underrun";
    `uvm_info("USB_TX_UNDERRUN", "Contention removed; starting the valid bulk IN retry", UVM_LOW)
    retry_sequence.start(p_sequencer.host_sequencer);
    if (!retry_sequence.completed) begin
      `uvm_fatal("USB_TX_UNDERRUN", "Bulk IN retry returned incomplete")
    end
    wait_for_endpoint_interrupt(endpoint, scenario_timeout);
    read_endpoint_entry(endpoint, entry);
    if (entry.active !== 1'b0 || entry.nbytes !== 0) begin
      `uvm_fatal("USB_TX_UNDERRUN", $sformatf("Bulk IN descriptor did not retire after retry: %s", describe_entry(entry)))
    end

    completed = 1'b1;
    `uvm_info("USB_TX_UNDERRUN", "Corrupted underrun CRC and successful bulk IN retry verified", UVM_LOW)
  endtask
endclass
