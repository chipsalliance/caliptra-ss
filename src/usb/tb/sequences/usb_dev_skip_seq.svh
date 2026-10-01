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
// Replaces the subsystem USB endpoint-skip firmware with UVM frontdoor
// activity, and exercises the USB DMA endpoint-skip datapath. Enumeration is
// reused by starting usb_init_seq as a child sequence, and all generic
// endpoint mechanics come from usb_base_seq.
//
// Scenario:
//
//   1. Run usb_init_seq as a child to enumerate the device at the configured
//      address and configuration 1.
//   2. Add the target endpoint to INTEN so the skip update and the later data
//      transfer both raise an observable interrupt.
//   3. Arm the endpoint with an Active entry, then set EPSKIP for it without
//      any USB traffic being directed at the endpoint.
//   4. Prove the skip update completed architecturally:
//        - EPSKIP self-clears for the endpoint within a bounded poll.
//        - The endpoint entry has only its Active bit cleared, so NBytes and
//          the buffer address are preserved.
//        - The endpoint's INTSTAT bit is set by the skip writeback.
//   5. Re-arm the endpoint over a sentinel-filled buffer and run
//      usb_dev_skip_host_seq to send one real bulk OUT transfer.
//   6. Prove the endpoint still works after the skip: the residual NBytes is
//      zero and every received byte matches the host payload.
//
// This drives the USB DMA FSM through IDLE -> READ_EPINFO_SKIP ->
// WAIT_ON_GNT_FOR_SKIP_UPDATE -> IDLE, which no other test in this
// bench reaches.
//
// The endpoint under test is resolved from the environment's endpoint
// configuration by protocol identity, so this sequence holds no anchor index,
// physical index, or endpoint-list offset of its own. Retargeting the scenario
// to a different endpoint is a change to skip_target_ep_number and the
// endpoint configuration.
//
// Checking placement: these are one-shot architectural checks of CSR and
// packet-memory state following directed stimulus, and this bench has no
// device-side predictor or scoreboard to host them. Continuous USB protocol
// checking remains active in the Synopsys host VIP throughout. A reusable
// endpoint-list and INTSTAT monitor would be the right home for these checks
// once more endpoint-management scenarios exist.
class usb_dev_skip_seq extends usb_base_seq;
  `uvm_object_utils(usb_dev_skip_seq)

  // Scenario knobs. A test or parent sequence may change any of these
  // before start().

  // Protocol identity of the endpoint this scenario skips and recovers. The
  // environment configuration supplies everything else about it.
  int unsigned skip_target_ep_number = 1;
  usb_direction_e skip_target_direction = USB_DIRECTION_OUT;

  // Packet-memory buffer (offset from DATABUFSTART) and its pre-fill pattern.
  logic [31:0] skip_buffer_offset = 32'h0000_0200;
  logic [31:0] recovery_sentinel = 32'hdede_dede;

  // Recovery transfer shape. This scenario owns both values and hands them to
  // usb_dev_skip_host_seq so the host and device sides cannot disagree.
  int unsigned recovery_bytes = 16;
  logic [7:0] recovery_payload_base = 8'ha0;

  // Bound each wait separately so a stalled skip is not hidden by the
  // scenario timeout.
  time skip_clear_timeout = 100us;
  time skip_clear_poll_interval = 100ns;
  time recovery_timeout = 500us;
  time recovery_poll_interval = 200ns;

  // Resolved once from the environment configuration at the start of
  // the scenario.
  usb_endpoint_cfg skip_endpoint;

  // Set only after every check in body() has passed.
  bit completed;

  function new(string name = "usb_dev_skip_seq");
    super.new(name);
  endfunction

  // Rebuild the little-endian packet-memory word the host payload produces at
  // the given byte offset within the recovery buffer.
  function logic [31:0] expected_payload_word(int unsigned byte_offset);
    logic [31:0] word;

    word = 32'h0;
    for (int unsigned lane = 0; lane < 4; lane++) begin
      logic [7:0] payload_byte;

      payload_byte = recovery_payload_base + byte_offset + lane;
      word[8*lane +: 8] = payload_byte;
    end
    return word;
  endfunction

  // Arm the endpoint, request a skip for it, and prove the skip update
  // completed with the architecturally required side effects.
  task run_skip_update_check();
    usb_ep_entry_t initial_entry;
    usb_ep_entry_t expected_entry;
    logic [31:0] interrupt_status;

    `uvm_info("USB_SKIP_SEQ", $sformatf("Starting the endpoint-skip check on %s over buffer 0x%03h for %0d bytes", skip_endpoint.convert2string(), skip_buffer_offset, recovery_bytes), UVM_LOW)

    // Clear any stale status so the check below observes only the interrupt
    // raised by this skip update.
    clear_endpoint_interrupt(skip_endpoint);
    arm_endpoint(skip_endpoint, recovery_bytes, skip_buffer_offset, initial_entry);
    expected_entry = initial_entry;
    expected_entry.active = 1'b0;

    // Hardware owns the skip request until the DMA performs the writeback, so
    // wait for self-clear instead of assuming a fixed completion latency.
    request_endpoint_skip(skip_endpoint);
    wait_for_endpoint_skip_clear(skip_endpoint, skip_clear_timeout, skip_clear_poll_interval);
    `uvm_info("USB_SKIP_SEQ", "EPSKIP self-cleared; checking the endpoint-entry writeback", UVM_LOW)

    // The skip writeback must clear only Active, leaving NBytes and the
    // buffer address intact for the endpoint's next transfer.
    check_endpoint_entry_writeback(skip_endpoint, expected_entry, "Skip writeback altered more than the Active bit");

    ral_read32("INTSTAT", p_sequencer.reg_model.combo.dev0_csr.INTSTAT, interrupt_status);
    if (!(interrupt_status & endpoint_intstat_mask(skip_endpoint))) begin
      `uvm_fatal("USB_SKIP_SEQ", $sformatf("Skip update did not assert INTSTAT.%s; INTSTAT=0x%08h", skip_endpoint.short_name(), interrupt_status))
    end
    clear_endpoint_interrupt(skip_endpoint);
    `uvm_info("USB_SKIP_SEQ", $sformatf("Endpoint-skip check passed: entry=0x%08h Active cleared, NBytes/address preserved, INTSTAT.%s asserted", expected_entry, skip_endpoint.short_name()), UVM_LOW)
  endtask

  // Fill the recovery buffer with a sentinel and hand the endpoint back to
  // hardware so it is armed before any host traffic arrives.
  task arm_recovery_transfer();
    usb_ep_entry_t recovery_entry;

    fill_endpoint_buffer(skip_buffer_offset, recovery_bytes, recovery_sentinel);
    arm_endpoint(skip_endpoint, recovery_bytes, skip_buffer_offset, recovery_entry);
    `uvm_info("USB_SKIP_SEQ", $sformatf("Re-armed %s after the skip over a buffer filled with 0x%08h", skip_endpoint.convert2string(), recovery_sentinel), UVM_LOW)
  endtask

  // Prove the previously skipped endpoint moved the full host payload into the
  // buffer it was armed with, overwriting the sentinel everywhere.
  task verify_recovery_transfer();
    usb_ep_entry_t observed_entry;
    logic [31:0] observed_word;
    logic [31:0] expected_word;

    read_endpoint_entry(skip_endpoint, observed_entry);
    if (observed_entry.nbytes !== 0) begin
      `uvm_fatal("USB_SKIP_SEQ", $sformatf("Post-skip transfer on %s left %0d residual bytes instead of 0; entry=%s", skip_endpoint.convert2string(), observed_entry.nbytes, describe_entry(observed_entry)))
    end

    for (int unsigned offset = 0; offset < recovery_bytes; offset += 4) begin
      expected_word = expected_payload_word(offset);
      read32(USB_DEV0_SRAM, skip_buffer_offset + offset, observed_word);
      if (observed_word !== expected_word) begin
        `uvm_fatal("USB_SKIP_SEQ", $sformatf("Post-skip payload mismatch at buffer offset 0x%03h: data=0x%08h expected=0x%08h", offset, observed_word, expected_word))
      end
    end
    `uvm_info("USB_SKIP_SEQ", $sformatf("Post-skip recovery verified: residual=0 and all %0d payload bytes match", recovery_bytes), UVM_LOW)
  endtask

  // Enumerate, exercise the endpoint skip, then prove the endpoint recovers.
  // Completion is published only after every check has already passed.
  virtual task body();
    usb_init_seq init_sequence;
    usb_dev_skip_host_seq host_sequence;

    completed = 1'b0;
    `uvm_info("USB_SKIP_SEQ", "Starting standalone USB endpoint-skip scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_SKIP_SEQ", "Enumeration did not complete, so the endpoint-skip scenario cannot start")
    end
    `uvm_info("USB_SKIP_SEQ", $sformatf("Enumeration complete at address %0d / configuration 1; starting endpoint-skip stimulus", p_sequencer.cfg.device_address), UVM_LOW)

    // Resolve the endpoint by protocol identity. A configuration that does not
    // advertise it fails here naming the endpoints that are advertised.
    skip_endpoint = get_endpoint(skip_target_ep_number, skip_target_direction);
    `uvm_info("USB_SKIP_SEQ", $sformatf("Endpoint-skip target resolved from the environment configuration: %s", skip_endpoint.convert2string()), UVM_LOW)
    check_buffer_clear_of_endpoint_list("Endpoint-skip", skip_buffer_offset, recovery_bytes);

    enable_endpoint_interrupt(skip_endpoint);
    run_skip_update_check();
    arm_recovery_transfer();

    host_sequence = usb_dev_skip_host_seq::type_id::create("skip_host_sequence");
    host_sequence.target_endpoint = skip_endpoint;
    host_sequence.payload_byte_count = recovery_bytes;
    host_sequence.payload_base = recovery_payload_base;
    host_sequence.device_address = p_sequencer.cfg.device_address;

    // The endpoint is armed before the host starts, so the transfer and the
    // device-side interrupt wait run concurrently without NAK-retry reliance.
    fork
      begin
        host_sequence.start(p_sequencer.host_sequencer);
        if (!host_sequence.completed) begin
          `uvm_fatal("USB_SKIP_SEQ", "Recovery host sequence returned incomplete")
        end
      end
      begin
        wait_for_endpoint_interrupt(skip_endpoint, recovery_timeout, recovery_poll_interval);
      end
    join

    verify_recovery_transfer();

    completed = 1'b1;
    `uvm_info("USB_SKIP_SEQ", "USB endpoint-skip scenario completed: skip writeback and post-skip recovery both verified", UVM_LOW)
  endtask
endclass
