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
//   1. Run usb_init_seq as a child to enumerate at address 1 / configuration 1.
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
// WAIT_ON_GNT_FOR_SKIP_UPDATE -> IDLE, which no other test in this bench
// reaches.
//
// The endpoint under test is resolved from the environment's endpoint profile
// by protocol identity, so this sequence holds no anchor index, physical
// index, or endpoint-list offset of its own. Retargeting the scenario to a
// different endpoint is a change to SKIP_TARGET_EP_NUMBER and the profile.
//
// Checking placement: these are one-shot architectural checks of CSR and
// packet-memory state following directed stimulus, and this bench has no
// device-side predictor or scoreboard to host them. Continuous USB protocol
// checking remains active in the Synopsys host VIP throughout. A reusable
// endpoint-list and INTSTAT monitor would be the right home for these checks
// once more endpoint-management scenarios exist.
class usb_dev_skip_seq extends usb_base_seq;
  `uvm_object_utils(usb_dev_skip_seq)

  // Protocol identity of the endpoint this scenario skips and recovers. The
  // environment profile supplies everything else about it.
  localparam int unsigned SKIP_TARGET_EP_NUMBER = 1;
  localparam usb_ep_dir_e SKIP_TARGET_EP_DIRECTION = USB_EP_DIR_OUT;

  localparam logic [31:0] SKIP_BUFFER_OFFSET = 32'h0000_0200;
  localparam logic [31:0] RECOVERY_SENTINEL = 32'hdede_dede;

  // Bound each wait separately so a stalled skip is not hidden by the
  // scenario timeout.
  localparam time SKIP_CLEAR_TIMEOUT = 100us;
  localparam time SKIP_CLEAR_POLL_INTERVAL = 100ns;
  localparam time RECOVERY_TIMEOUT = 500us;
  localparam time RECOVERY_POLL_INTERVAL = 200ns;

  // Resolved once from the environment profile at the start of the scenario.
  usb_endpoint_profile skip_endpoint;

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

      payload_byte = USB_DEV_SKIP_PAYLOAD_BASE + byte_offset + lane;
      word[8*lane +: 8] = payload_byte;
    end
    return word;
  endfunction

  // Arm the endpoint, request a skip for it, and prove the skip update
  // completed with the architecturally required side effects.
  task run_skip_update_check();
    logic [31:0] initial_entry;
    logic [31:0] expected_entry;
    logic [31:0] interrupt_status;

    `uvm_info("USB_SKIP_SEQ", $sformatf("Starting the endpoint-skip check on %s over buffer 0x%03h for %0d bytes", skip_endpoint.describe(), SKIP_BUFFER_OFFSET, USB_DEV_SKIP_RECOVERY_BYTES), UVM_LOW)

    // Clear any stale status so the check below observes only the interrupt
    // raised by this skip update.
    clear_endpoint_interrupt(skip_endpoint);
    arm_endpoint(skip_endpoint, USB_DEV_SKIP_RECOVERY_BYTES, SKIP_BUFFER_OFFSET, initial_entry);
    expected_entry = initial_entry & ~EP_ENTRY_ACTIVE;

    // Hardware owns the skip request until the DMA performs the writeback, so
    // wait for self-clear instead of assuming a fixed completion latency.
    request_endpoint_skip(skip_endpoint);
    wait_for_endpoint_skip_clear(skip_endpoint, SKIP_CLEAR_TIMEOUT, SKIP_CLEAR_POLL_INTERVAL);
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
    logic [31:0] recovery_entry;

    fill_endpoint_buffer(SKIP_BUFFER_OFFSET, USB_DEV_SKIP_RECOVERY_BYTES, RECOVERY_SENTINEL);
    arm_endpoint(skip_endpoint, USB_DEV_SKIP_RECOVERY_BYTES, SKIP_BUFFER_OFFSET, recovery_entry);
    `uvm_info("USB_SKIP_SEQ", $sformatf("Re-armed %s after the skip over a buffer filled with 0x%08h", skip_endpoint.describe(), RECOVERY_SENTINEL), UVM_LOW)
  endtask

  // Prove the previously skipped endpoint moved the full host payload into the
  // buffer it was armed with, overwriting the sentinel everywhere.
  task verify_recovery_transfer();
    logic [31:0] observed_entry;
    logic [31:0] observed_word;
    logic [31:0] expected_word;
    int unsigned residual_bytes;

    read_endpoint_entry(skip_endpoint, observed_entry);
    residual_bytes = entry_residual_bytes(observed_entry);
    if (residual_bytes !== 0) begin
      `uvm_fatal("USB_SKIP_SEQ", $sformatf("Post-skip transfer on %s left %0d residual bytes instead of 0; entry=0x%08h", skip_endpoint.describe(), residual_bytes, observed_entry))
    end

    for (int unsigned offset = 0; offset < USB_DEV_SKIP_RECOVERY_BYTES; offset += 4) begin
      expected_word = expected_payload_word(offset);
      read32(USB_DEV0_SRAM, SKIP_BUFFER_OFFSET + offset, observed_word);
      if (observed_word !== expected_word) begin
        `uvm_fatal("USB_SKIP_SEQ", $sformatf("Post-skip payload mismatch at buffer offset 0x%03h: data=0x%08h expected=0x%08h", offset, observed_word, expected_word))
      end
    end
    `uvm_info("USB_SKIP_SEQ", $sformatf("Post-skip recovery verified: residual=0 and all %0d payload bytes match", USB_DEV_SKIP_RECOVERY_BYTES), UVM_LOW)
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
    `uvm_info("USB_SKIP_SEQ", "Enumeration complete at address 1 / configuration 1; starting endpoint-skip stimulus", UVM_LOW)

    // Resolve the endpoint by protocol identity. A profile that does not
    // advertise it fails here naming the endpoints that are advertised.
    skip_endpoint = get_endpoint(SKIP_TARGET_EP_NUMBER, SKIP_TARGET_EP_DIRECTION);
    `uvm_info("USB_SKIP_SEQ", $sformatf("Endpoint-skip target resolved from the environment profile: %s", skip_endpoint.describe()), UVM_LOW)

    enable_endpoint_interrupt(skip_endpoint);
    run_skip_update_check();
    arm_recovery_transfer();

    host_sequence = usb_dev_skip_host_seq::type_id::create("skip_host_sequence");
    host_sequence.target_endpoint = skip_endpoint;

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
        wait_for_endpoint_interrupt(skip_endpoint, RECOVERY_TIMEOUT, RECOVERY_POLL_INTERVAL);
      end
    join

    verify_recovery_transfer();

    completed = 1'b1;
    `uvm_info("USB_SKIP_SEQ", "USB endpoint-skip scenario completed: skip writeback and post-skip recovery both verified", UVM_LOW)
  endtask
endclass
