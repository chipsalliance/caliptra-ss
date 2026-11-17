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
// Runs the double-buffer bulk scenario while two background threads keep issuing
// AXI write/read pairs to scratch storage the USB endpoints never use:
//   - DEV0 RAM through the DEV0 memory AXI-to-AHB bridge, and
//   - Hub descriptor storage through the Combo AXI-to-AHB bridge (the Hub stays
//     disabled/disconnected, as the hardware spec requires before modifying it).
// The base scenario checks the USB payloads; this sequence checks every AXI
// response and readback beat, and proves that AXI requests on each bridge were
// outstanding on the bus while USB DATA packets moved through the device.
class usb_axi_during_usb_traffic_seq extends usb_double_buffer_bulk_seq;
  `uvm_object_utils(usb_axi_during_usb_traffic_seq)

  localparam logic [31:0] SCRATCH_OFFSET = 32'h0000_8000;
  localparam int unsigned SCRATCH_BYTES = 'h1000;
  localparam int unsigned SLOT_BYTES = 64;
  localparam int unsigned MAX_GAP_CYCLES = 8;
  localparam logic [31:0] HUB_ACTIVE_MASK = 32'h0001_0001;

  int unsigned axi_pairs;
  int unsigned axi_beats;
  int unsigned hub_pairs;
  int unsigned hub_beats;
  int unsigned tx_data_packets;
  int unsigned rx_data_packets;
  int unsigned tx_overlapped;
  int unsigned rx_overlapped;
  int unsigned tx_hub_overlapped;
  int unsigned rx_hub_overlapped;

  protected usb_axi_inflight_callbacks bus_tracker;
  protected usb_axi_inflight_callbacks hub_tracker;
  protected uvm_reg_addr_t scratch_base;
  protected uvm_reg_addr_t hub_scratch_base;
  protected logic [31:0] hub_scratch_offset;
  protected int unsigned hub_slots;

  function new(string name = "usb_axi_during_usb_traffic_seq");
    super.new(name);
  endfunction

  protected task issue_scratch_request(usb_target_e target, aaxi_master_tr request, string kind, int unsigned pair);
    usb_axi_single_request_seq child;

    child = usb_axi_single_request_seq::type_id::create($sformatf("scratch_%s_%s%0d", usb_target_name(target), kind, pair));
    child.target = target;
    child.transaction = request;
    child.start(p_sequencer, this);
  endtask

  // One INCR write of random data to a random 64-byte slot, then a checked readback of the same footprint.
  protected task scratch_write_read(usb_target_e target);
    aaxi_master_tr request;
    logic [31:0] offset;
    logic [31:0] written[];
    logic [31:0] actual;
    int unsigned beats;
    int unsigned pair;
    string label;

    beats = $urandom_range(16, 1);
    if (target == USB_HUB) begin
      label = "Hub";
      pair = hub_pairs;
      offset = hub_scratch_offset + SLOT_BYTES * $urandom_range(hub_slots - 1, 0);
    end else begin
      label = "RAM";
      pair = axi_pairs;
      offset = SCRATCH_OFFSET + SLOT_BYTES * $urandom_range(SCRATCH_BYTES / SLOT_BYTES - 1, 0);
    end
    check_address(target, offset);
    check_address(target, offset + 4 * (beats - 1));
    written = new[beats];
    foreach (written[beat]) written[beat] = $urandom();

    request = create_transaction(target, offset, 1'b1, written[0], null);
    request.len = beats - 1;
    request.data.delete();
    request.strobes.delete();
    request.wuser_A = new[beats];
    foreach (written[beat]) begin
      request.wuser_A[beat] = request.awuser;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        request.data.push_back(written[beat][lane * 8 +: 8]);
        request.strobes.push_back(1'b1);
      end
    end
    issue_scratch_request(target, request, "write", pair);
    if (request.resp !== AAXI_RESP_OKAY) begin
      `uvm_fatal("USB_AXI_DURING_USB", $sformatf("%s scratch write %0d AXI=0x%016h INCR-%0d expected_resp=%0h actual_resp=%0h", label, pair, request.addr, beats, AAXI_RESP_OKAY, request.resp))
    end

    request = create_transaction(target, offset, 1'b0, '0, null);
    request.len = beats - 1;
    issue_scratch_request(target, request, "read", pair);
    if (request.rresp_Q.size() != beats || request.data.size() != beats * 4) begin
      `uvm_fatal("USB_AXI_DURING_USB", $sformatf("%s scratch read %0d AXI=0x%016h returned %0d responses/%0d bytes for %0d beats", label, pair, request.addr, request.rresp_Q.size(), request.data.size(), beats))
    end
    foreach (written[beat]) begin
      if (request.rresp_Q[beat] !== AAXI_RESP_OKAY) begin
        `uvm_fatal("USB_AXI_DURING_USB", $sformatf("%s scratch read %0d beat=%0d/%0d AXI=0x%016h expected_resp=%0h actual_resp=%0h", label, pair, beat, beats, request.addr, AAXI_RESP_OKAY, request.rresp_Q[beat]))
      end
      for (int unsigned lane = 0; lane < 4; lane++) actual[lane * 8 +: 8] = request.data[beat * 4 + lane];
      if (actual !== written[beat]) begin
        `uvm_fatal("USB_AXI_DURING_USB", $sformatf("%s scratch read %0d beat=%0d/%0d offset=0x%08h AXI=0x%016h expected=0x%08h actual=0x%08h", label, pair, beat, beats, offset + 4 * beat, request.addr + 4 * beat, written[beat], actual))
      end
    end
    if (target == USB_HUB) begin
      hub_pairs++;
      hub_beats += beats;
    end else begin
      axi_pairs++;
      axi_beats += beats;
    end
  endtask

  // Other traffic shares these managers, so match accepted-but-incomplete addresses to the scratch window.
  protected function bit scratch_outstanding(usb_axi_inflight_callbacks tracker, uvm_reg_addr_t window_base, int unsigned window_bytes);
    foreach (tracker.read_addresses[id]) begin
      foreach (tracker.read_addresses[id][index]) begin
        if (tracker.read_addresses[id][index] - window_base < window_bytes) return 1'b1;
      end
    end
    foreach (tracker.write_addresses[id]) begin
      foreach (tracker.write_addresses[id][index]) begin
        if (tracker.write_addresses[id][index] - window_base < window_bytes) return 1'b1;
      end
    end
    return 1'b0;
  endfunction

  // Count DATA packets in each direction and those that finished while a scratch request was on each bus.
  protected task count_data_packets(bit host_tx);
    svt_usb_agent host_agent;
    uvm_object packet_object;
    svt_usb_packet packet;
    bit ram_overlapped;
    bit hub_overlapped;

    if (!$cast(host_agent, p_sequencer.host_sequencer.get_parent()) || host_agent.prot == null) begin
      `uvm_fatal("USB_AXI_DURING_USB", "Unable to resolve the SVT host agent protocol component")
    end
    forever begin
      if (host_tx) host_agent.prot.NOTIFY_20_HOST_TX_PACKET.wait_trigger_data(packet_object);
      else host_agent.prot.NOTIFY_20_HOST_RX_PACKET.wait_trigger_data(packet_object);
      if (!$cast(packet, packet_object) || packet == null) continue;
      if (!(packet.get_pid_name_val() inside {svt_usb_packet::DATA0, svt_usb_packet::DATA1})) continue;
      ram_overlapped = scratch_outstanding(bus_tracker, scratch_base, SCRATCH_BYTES);
      hub_overlapped = scratch_outstanding(hub_tracker, hub_scratch_base, hub_slots * SLOT_BYTES);
      if (host_tx) begin
        tx_data_packets++;
        tx_overlapped += ram_overlapped;
        tx_hub_overlapped += hub_overlapped;
      end else begin
        rx_data_packets++;
        rx_overlapped += ram_overlapped;
        rx_hub_overlapped += hub_overlapped;
      end
    end
  endtask

  virtual task body();
    aaxi_sequencer manager_sequencer;
    aaxi_sequencer combo_sequencer;
    uvm_mem hub_storage;
    process monitors[$];
    bit usb_done;

    check_buffer_clear_of_endpoint_list("AXI scratch", SCRATCH_OFFSET, SCRATCH_BYTES);
    manager_sequencer = sequencer_for(USB_DEV0_SRAM);
    scratch_base = map_for(USB_DEV0_SRAM).get_base_addr(UVM_NO_HIER) + SCRATCH_OFFSET;

    // Hub scratch: whole 64-byte slots of DESCRIPTOR_HIGH; the double-buffer scenario never uses the Hub.
    hub_storage = p_sequencer.reg_model.combo.hub.DESCRIPTOR_HIGH.m_mem;
    hub_scratch_offset = mem_word_offset(USB_HUB, hub_storage, 0);
    hub_slots = hub_storage.get_size() * 4 / SLOT_BYTES;
    if (hub_slots == 0) `uvm_fatal("USB_AXI_DURING_USB", "Hub DESCRIPTOR_HIGH is smaller than one scratch slot")
    hub_scratch_base = map_for(USB_HUB).get_base_addr(UVM_NO_HIER) + hub_scratch_offset;
    combo_sequencer = sequencer_for(USB_HUB);
    // CaliptraSSHardwareSpecification: Hub must be disabled/disconnected before descriptor storage is modified.
    expect32(USB_HUB, reg_offset(USB_HUB, p_sequencer.reg_model.combo.hub.CONTROL), '0, HUB_ACTIVE_MASK);

    // Attach before any traffic so every completion has a recorded acceptance.
    bus_tracker = usb_axi_inflight_callbacks::type_id::create("axi_during_usb_tracker");
    manager_sequencer.cfg.agent.add_callback(bus_tracker);
    hub_tracker = usb_axi_inflight_callbacks::type_id::create("hub_during_usb_tracker");
    combo_sequencer.cfg.agent.add_callback(hub_tracker);

    fork
      begin
        monitors.push_back(process::self());
        count_data_packets(1'b1);
      end
      begin
        monitors.push_back(process::self());
        count_data_packets(1'b0);
      end
    join_none

    fork
      begin
        super.body();
        usb_done = 1'b1;
      end
      while (!usb_done) begin
        scratch_write_read(USB_DEV0_SRAM);
        repeat ($urandom_range(MAX_GAP_CYCLES, 0)) p_sequencer.cfg.wait_bus_negedge();
      end
      while (!usb_done) begin
        scratch_write_read(USB_HUB);
        repeat ($urandom_range(MAX_GAP_CYCLES, 0)) p_sequencer.cfg.wait_bus_negedge();
      end
    join

    foreach (monitors[index]) monitors[index].kill();
    manager_sequencer.cfg.agent.delete_callback(bus_tracker);
    combo_sequencer.cfg.agent.delete_callback(hub_tracker);
    if (bus_tracker.reads != 0 || bus_tracker.writes != 0) begin
      `uvm_fatal("USB_AXI_DURING_USB", $sformatf("DEV0 RAM requests remain outstanding: reads=%0d writes=%0d", bus_tracker.reads, bus_tracker.writes))
    end
    if (hub_tracker.reads != 0 || hub_tracker.writes != 0) begin
      `uvm_fatal("USB_AXI_DURING_USB", $sformatf("Combo requests remain outstanding: reads=%0d writes=%0d", hub_tracker.reads, hub_tracker.writes))
    end
    if (!completed) return;
    completed = 1'b0;
    `uvm_info("USB_AXI_DURING_USB", $sformatf("Scratch AXI: RAM %0d write/read pairs, %0d beats checked; Hub %0d write/read pairs, %0d beats checked; DATA packets host-TX=%0d (with RAM AXI outstanding=%0d, Hub AXI outstanding=%0d) host-RX=%0d (with RAM AXI outstanding=%0d, Hub AXI outstanding=%0d)", axi_pairs, axi_beats, hub_pairs, hub_beats, tx_data_packets, tx_overlapped, tx_hub_overlapped, rx_data_packets, rx_overlapped, rx_hub_overlapped), UVM_LOW)
    if (tx_overlapped == 0 || rx_overlapped == 0) begin
      `uvm_fatal("USB_AXI_DURING_USB", "No DATA packet in one direction finished while a RAM scratch AXI request was outstanding")
    end
    if (tx_hub_overlapped == 0 || rx_hub_overlapped == 0) begin
      `uvm_fatal("USB_AXI_DURING_USB", "No DATA packet in one direction finished while a Hub scratch AXI request was outstanding")
    end
    completed = 1'b1;
  endtask
endclass
