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
class usb_axi_combo_access_seq extends usb_axi_bridge_base_seq;
  `uvm_object_utils(usb_axi_combo_access_seq)

  typedef enum {COMBO_OKAY, COMBO_ERROR, COMBO_OBSERVE} response_expectation_e;
  typedef enum {COMBO_FIXED, COMBO_INCR, COMBO_WRAP} combo_burst_e;

  protected logic [31:0] offsets[3];
  protected logic [31:0] masks[3] = '{USB_DEV0_ROUTE_MASK, '1, '1};
  protected string region_names[3] = '{"DEV0-CSR", "OCP-Recovery", "Hub"};
  protected logic [31:0] hub_end;
  protected logic [31:0] combo_bytes;
  protected logic [31:0] hub_high_offset;
  protected int unsigned checked_words, positive_pairs;
  protected int unsigned expected_errors, error_recoveries, write_probes;

  function new(string name = "usb_axi_combo_access_seq");
    super.new(name);
  endfunction

  protected function aaxi_master_tr make_request(string label, logic [31:0] offset, bit is_write, logic [31:0] first_word = '0, int unsigned beats = 1, int unsigned size = 2, combo_burst_e burst = COMBO_INCR);
    aaxi_master_tr request;
    logic [31:0] data;

    // Select the Combo manager without applying the DEV0-CSR-only address guard.
    request = create_transaction(USB_DEV0_CSR, offset, is_write, first_word, authorized_user);
    request.set_name(label);
    request.len = beats - 1;
    request.size = size;
    case (burst)
      COMBO_FIXED: request.burst = AAXI_BURST_FIXED;
      COMBO_INCR:  request.burst = AAXI_BURST_INCR;
      COMBO_WRAP:  request.burst = AAXI_BURST_WRAP;
    endcase
    request.wuser_A = new[beats];
    foreach (request.wuser_A[beat]) request.wuser_A[beat] = authorized_user.value;
    if (is_write) begin
      request.data.delete();
      request.strobes.delete();
      for (int unsigned beat = 0; beat < beats; beat++) begin
        data = beat == 0 ? first_word : $urandom();
        for (int unsigned lane = 0; lane < (1 << size); lane++) begin
          request.data.push_back(data[lane * 8 +: 8]);
          request.strobes.push_back(1'b1);
        end
      end
    end
    return request;
  endfunction

  protected function bit check_response(aaxi_master_tr request, response_expectation_e expected = COMBO_OKAY);
    logic [1:0] response;
    bit is_write = request.kind == AAXI_WRITE;
    int unsigned count = is_write ? 1 : int'(request.len) + 1;
    string responses = is_write ? $sformatf("BRESP=%0h", request.resp) : $sformatf("RRESP=%p", request.rresp_Q);

    if (!is_write && request.rresp_Q.size() != count) begin
      `uvm_fatal("USB_COMBO_RESPONSE", $sformatf("%s AXI=0x%016h: received %0d/%0d read responses", request.get_name(), request.addr, request.rresp_Q.size(), count))
    end
    if (expected == COMBO_OBSERVE) begin
      `uvm_info("USB_COMBO_OBSERVE", $sformatf("%s %s AXI=0x%016h SIZE=%0d BURST=%0h beats=%0d %s bytes=%p strobes=%p", request.get_name(), is_write ? "write" : "read", request.addr, request.size, request.burst, int'(request.len) + 1, responses, request.data, request.strobes), UVM_LOW)
      return 1'b1;
    end
    for (int unsigned beat = 0; beat < count; beat++) begin
      response = is_write ? request.resp : request.rresp_Q[beat];
      if ((expected == COMBO_OKAY && response !== AAXI_RESP_OKAY) ||
          (expected == COMBO_ERROR && response !== AAXI_RESP_SLVERR && response !== AAXI_RESP_DECERR)) begin
        `uvm_error("USB_COMBO_RESPONSE", $sformatf("%s %s AXI=0x%016h USER=0x%08h SIZE=%0d BURST=%0h beat=%0d/%0d expected=%s actual_resp=%0h", request.get_name(), is_write ? "write" : "read", request.addr, authorized_user.value, request.size, request.burst, beat, count, expected.name(), response))
        return 1'b0;
      end
      if (expected == COMBO_ERROR) expected_errors++;
    end
    return 1'b1;
  endfunction

  protected function aaxi_master_tr linear_footprint(aaxi_master_tr request, bit is_write);
    uvm_reg_addr_t first;
    int unsigned words;

    burst_span(aaxi_burst_type'(request.burst), request.addr - base_address, int'(request.len) + 1, first, words);
    return make_request({request.get_name(), "-linear"}, 32'(first), is_write, is_write ? $urandom() : '0, words);
  endfunction

  protected function void compare_read(aaxi_master_tr actual, aaxi_master_tr written, logic [31:0] mask = '1);
    logic [31:0] expected_word, actual_word;
    uvm_reg_addr_t address;
    int unsigned bytes = 4 * (int'(actual.len) + 1);
    int unsigned written_bytes = 4 * (int'(written.len) + 1);
    int expected_beat;

    if (actual.data.size() != bytes || written.data.size() != written_bytes) begin
      `uvm_fatal("USB_COMBO_DATA", $sformatf("%s: expected read/write bytes=%0d/%0d, actual=%0d/%0d", actual.get_name(), bytes, written_bytes, actual.data.size(), written.data.size()))
    end
    for (int unsigned beat = 0; beat <= int'(actual.len); beat++) begin
      address = beat_address(actual, beat);
      expected_beat = -1;
      // The last matching write beat wins when FIXED repeats an address.
      for (int unsigned index = 0; index <= int'(written.len); index++) begin
        if (beat_address(written, index) == address) expected_beat = int'(index);
      end
      if (expected_beat < 0) begin
        `uvm_fatal("USB_COMBO_DATA", $sformatf("%s: no initialized expected word at AXI=0x%016h", actual.get_name(), address))
        return;
      end
      expected_word = data_word(written, expected_beat) & mask;
      actual_word = data_word(actual, beat) & mask;
      if (actual_word !== expected_word) begin
        `uvm_fatal("USB_COMBO_DATA", $sformatf("%s AXI=0x%016h BURST=%0h beat=%0d expected=0x%08h actual=0x%08h mask=0x%08h", actual.get_name(), address, actual.burst, beat, expected_word, actual_word, mask))
      end
      checked_words++;
    end
  endfunction

  protected task write_read_word(int unsigned region, logic [31:0] value, output bit passed);
    aaxi_master_tr written, readback;

    passed = 1'b0;
    written = make_request(region_names[region], offsets[region], 1'b1, value & masks[region]);
    issue_request(written);
    if (!check_response(written)) return;
    readback = make_request(region_names[region], offsets[region], 1'b0);
    issue_request(readback);
    if (!check_response(readback)) return;
    compare_read(readback, written, masks[region]);
    positive_pairs++;
    passed = 1'b1;
    `uvm_info("USB_COMBO_DATA", $sformatf("PASS %s AXI=0x%016h expected=0x%08h actual=0x%08h mask=0x%08h", region_names[region], readback.addr, data_word(written, 0), data_word(readback, 0), masks[region]), UVM_LOW)
  endtask

  protected task write_read_burst(string label, logic [31:0] offset, int unsigned beats, combo_burst_e burst);
    aaxi_master_tr written, readback;

    written = make_request(label, offset, 1'b1, $urandom(), beats, 2, burst);
    issue_request(written);
    if (!check_response(written)) return;
    // Linear readback prevents matching WRAP write/read address bugs from canceling.
    if (burst == COMBO_WRAP) begin
      readback = linear_footprint(written, 1'b0);
      issue_request(readback);
      if (!check_response(readback)) return;
      compare_read(readback, written);
    end
    readback = make_request(label, offset, 1'b0, '0, beats, 2, burst);
    issue_request(readback);
    if (!check_response(readback)) return;
    compare_read(readback, written);
    `uvm_info("USB_COMBO_BURST", $sformatf("PASS %s %s offset=0x%08h beats=%0d", label, burst.name(), offset, beats), UVM_LOW)
  endtask

  protected task run_burst_cases();
    int unsigned fixed_lengths[3] = '{1, 2, 16};
    int unsigned wrap_lengths[4] = '{2, 4, 8, 16};

    foreach (fixed_lengths[index]) begin
      write_read_burst($sformatf("FIXED-%0d", fixed_lengths[index]), hub_high_offset, fixed_lengths[index], COMBO_FIXED);
    end
    foreach (wrap_lengths[index]) begin
      write_read_burst($sformatf("WRAP-%0d", wrap_lengths[index]), hub_high_offset + 4 * (wrap_lengths[index] - 1), wrap_lengths[index], COMBO_WRAP);
    end
  endtask

  protected task run_unmapped_cases();
    logic [31:0] holes[4] = '{32'h40, 32'h7fc, hub_end, combo_bytes - 4};
    aaxi_master_tr request;
    bit negative_ok, positive_ok;

    foreach (holes[index]) begin
      if (index >= 2 && hub_end == combo_bytes) continue;
      for (int unsigned direction = 0; direction < 2; direction++) begin
        request = make_request("unmapped", holes[index], direction == 1, $urandom());
        issue_request(request);
        negative_ok = check_response(request, COMBO_ERROR);
        `uvm_info("USB_COMBO_DECODE", $sformatf("Unmapped AXI=0x%016h %s expected_SLVERR_or_DECERR=%0b", request.addr, direction == 1 ? $sformatf("BRESP=%0h", request.resp) : $sformatf("RRESP=%p", request.rresp_Q), negative_ok), UVM_LOW)
        write_read_word(index % 3, $urandom(), positive_ok);
        if (negative_ok && positive_ok) error_recoveries++;
      end
    end
  endtask

  protected task run_observations();
    logic [31:0] edges[2] = '{32'h40, hub_end};
    aaxi_master_tr request;
    bit seeded;

    foreach (edges[index]) begin
      if (index == 1 && hub_end == combo_bytes) continue;
      request = make_request(index == 0 ? "CSR-end-crossing" : "Hub-end-crossing", edges[index] - 4, 1'b0, '0, 2);
      issue_request(request);
      void'(check_response(request, COMBO_OBSERVE));
      if (request.rresp_Q[1] !== AAXI_RESP_SLVERR && request.rresp_Q[1] !== AAXI_RESP_DECERR) begin
        `uvm_error("USB_COMBO_RESPONSE", $sformatf("%s crossed into unmapped offset 0x%08h without an error: RRESP[1]=%0h", request.get_name(), edges[index], request.rresp_Q[1]))
      end else expected_errors++;
    end
    request = make_request("outside-Combo-aperture", combo_bytes + offsets[0], 1'b0);
    issue_request(request);
    void'(check_response(request, COMBO_OBSERVE));

    `uvm_info("USB_COMBO_OBSERVE", "AxSIZE=0/1 are AXI-legal but unsupported by USB: characterize responses/data, without requiring acceptance or byte preservation. AxSIZE=2 is checked by the normal DWORD cases.", UVM_LOW)
    foreach (offsets[region]) begin
      for (int unsigned size = 0; size < 2; size++) begin
        write_read_word(region, 32'ha1b2_c3d4, seeded);
        if (!seeded) continue;
        request = make_request($sformatf("%s-narrow-write", region_names[region]), offsets[region], 1'b1, 32'h5e6f, 1, size);
        issue_request(request);
        void'(check_response(request, COMBO_OBSERVE));
        request = make_request($sformatf("%s-narrow-read", region_names[region]), offsets[region], 1'b0, '0, 1, size);
        issue_request(request);
        void'(check_response(request, COMBO_OBSERVE));
        request = make_request($sformatf("%s-DWORD-after-size%0d", region_names[region], size), offsets[region], 1'b0);
        issue_request(request);
        if (check_response(request)) begin
          if (request.data.size() != 4) `uvm_fatal("USB_COMBO_DATA", "Post-probe DWORD read did not return four bytes")
          `uvm_info("USB_COMBO_OBSERVE", $sformatf("%s: before=0x%08h after=0x%08h", request.get_name(), 32'ha1b2_c3d4 & masks[region], data_word(request, 0)), UVM_LOW)
        end
      end
    end
  endtask

  // AXI A6.3 keeps a Peripheral-region transaction inside its region, and no spec defines
  // the mapped beat at these edges or any address beyond the Combo window, so those effects
  // are observed. As with the read crossings, a write touching an Unmapped offset must return
  // SLVERR/DECERR, and every probe must complete and leave normal accesses working.
  protected task run_write_observations();
    logic [31:0] edges[3] = '{32'h40, 32'h800, hub_end};
    string labels[3] = '{"CSR-end-crossing-write", "Unmapped-to-Recovery-crossing-write", "Hub-end-crossing-write"};
    logic [31:0] mapped_offset, seed, attempted, actual;
    aaxi_master_tr request, before_tr, after_tr;
    int unsigned mapped_beat;
    string outcome;
    bit negative_ok, positive_ok, seeded;

    foreach (edges[index]) begin
      if (index == 2 && hub_end == combo_bytes) continue;
      // The Recovery crossing starts in the hole; the other two start on the mapped side.
      mapped_beat = index == 1 ? 1 : 0;
      mapped_offset = edges[index] - 4 + 4 * mapped_beat;
      before_tr = make_request({labels[index], "-mapped-before"}, mapped_offset, 1'b0);
      issue_request(before_tr);
      void'(check_response(before_tr, COMBO_OBSERVE));
      request = make_request(labels[index], edges[index] - 4, 1'b1, $urandom(), 2);
      issue_request(request);
      negative_ok = check_response(request, COMBO_ERROR);
      write_probes++;
      after_tr = make_request({labels[index], "-mapped-after"}, mapped_offset, 1'b0);
      issue_request(after_tr);
      void'(check_response(after_tr, COMBO_OBSERVE));
      `uvm_info("USB_COMBO_OBSERVE", $sformatf("%s AXI=0x%016h BRESP=%0h; mapped beat offset=0x%08h before=0x%08h written=0x%08h after=0x%08h", labels[index], request.addr, request.resp, mapped_offset, before_tr.data.size() == 4 ? data_word(before_tr, 0) : 'x, data_word(request, mapped_beat), after_tr.data.size() == 4 ? data_word(after_tr, 0) : 'x), UVM_LOW)
      write_read_word(index, $urandom(), positive_ok);
      if (negative_ok && positive_ok) error_recoveries++;
    end

    foreach (offsets[region]) begin
      seed = $urandom() & masks[region];
      write_read_word(region, seed, seeded);
      if (!seeded) continue;
      attempted = ~seed & masks[region];
      request = make_request($sformatf("outside-Combo-%s-write", region_names[region]), combo_bytes + offsets[region], 1'b1, attempted);
      issue_request(request);
      void'(check_response(request, COMBO_OBSERVE));
      write_probes++;
      after_tr = make_request($sformatf("%s-after-outside-write", region_names[region]), offsets[region], 1'b0);
      issue_request(after_tr);
      if (!check_response(after_tr)) continue;
      if (after_tr.data.size() != 4) `uvm_fatal("USB_COMBO_DATA", "In-window read did not return four bytes")
      actual = data_word(after_tr, 0) & masks[region];
      outcome = actual === seed ? "unchanged" : actual === attempted ? "aliased into the window" : "neither seed nor written value";
      `uvm_info("USB_COMBO_OBSERVE", $sformatf("Outside-window write AXI=0x%016h BRESP=%0h; in-window %s AXI=0x%016h seed=0x%08h written=0x%08h actual=0x%08h mask=0x%08h: %s", request.addr, request.resp, region_names[region], after_tr.addr, seed, attempted, actual, masks[region], outcome), UVM_LOW)
      write_read_word(region, $urandom(), positive_ok);
    end
  endtask

  protected task run_random_accesses();
    aaxi_master_tr requests[], seeds[], readback;
    bit is_write[], seeded[];
    int unsigned issue_gaps[];
    combo_burst_e burst;
    int unsigned request_count, beats, gap_cycles;
    int unsigned response_stall = 256;
    int unsigned max_reads, max_writes;
    logic [31:0] offset;
    bit write_choice, tracking, overlap;
    bit passed = 1'b1;
    aaxi_sequencer manager;
    usb_axi_inflight_callbacks tracker;
    realtime clock_sample;
    time request_timeout;

    if (!std::randomize(request_count) with { request_count inside {[2:10]}; }) begin
      `uvm_fatal("USB_COMBO_RANDOM", "Request-count randomization failed")
    end
    requests = new[request_count];
    seeds = new[request_count];
    is_write = new[request_count];
    seeded = new[request_count];
    issue_gaps = new[request_count];
    foreach (requests[index]) begin
      if (!std::randomize(burst, beats, write_choice, gap_cycles) with {
        burst inside {COMBO_FIXED, COMBO_INCR, COMBO_WRAP};
        solve burst before beats;
        if (burst == COMBO_WRAP) beats inside {2, 4, 8, 16};
        else beats inside {[1:16]};
        if (index == 1) write_choice != is_write[0];
        gap_cycles inside {[0:4]};
      }) begin
        `uvm_fatal("USB_COMBO_RANDOM", $sformatf("Request %0d randomization failed", index))
      end
      // Each disjoint 64-byte slot contains any selected DWORD burst footprint.
      offset = hub_high_offset + 64 * index;
      if (burst == COMBO_WRAP) offset += 4 * (beats - 1);
      requests[index] = make_request($sformatf("random-%0d", index), offset, write_choice, $urandom(), beats, 2, burst);
      is_write[index] = write_choice;
      issue_gaps[index] = gap_cycles;
      `uvm_info("USB_COMBO_RANDOM", $sformatf("random-%0d write=%0b burst=%s offset=0x%08h beats=%0d gap=%0d cycles", index, write_choice, burst.name(), offset, beats, gap_cycles), UVM_LOW)
      if (!write_choice) begin
        seeds[index] = linear_footprint(requests[index], 1'b1);
        issue_request(seeds[index]);
        seeded[index] = check_response(seeds[index]);
      end
    end
    p_sequencer.cfg.wait_bus_negedge();
    clock_sample = $realtime;
    p_sequencer.cfg.wait_bus_negedge();
    request_timeout = transfer_timeout() + time'(request_count * 16 * response_stall * ($realtime - clock_sample));
    manager = sequencer_for(USB_DEV0_CSR);
    tracker = usb_axi_inflight_callbacks::type_id::create("combo_random_tracker");
    manager.cfg.agent.add_callback(tracker);
    tracking = 1'b1;
    fork
      begin
        while (tracking) begin
          p_sequencer.cfg.wait_bus_negedge();
          if (tracker.reads > max_reads) max_reads = tracker.reads;
          if (tracker.writes > max_writes) max_writes = tracker.writes;
          if (tracker.reads > 0 && tracker.writes > 0) overlap = 1'b1;
        end
      end
      begin
        foreach (requests[index]) begin
          automatic int slot = index;
          repeat (issue_gaps[index]) p_sequencer.cfg.wait_bus_negedge();
          fork
            issue_request(requests[slot], response_stall, request_timeout);
          join_none
        end
        wait fork;
        p_sequencer.cfg.wait_bus_negedge();
        tracking = 1'b0;
      end
    join
    manager.cfg.agent.delete_callback(tracker);
    if (!overlap || tracker.accepted != request_count || tracker.reads != 0 || tracker.writes != 0) begin
      `uvm_fatal("USB_COMBO_RANDOM", $sformatf("Missing overlap/completion: overlap=%0b accepted=%0d/%0d pending=%0d/%0d", overlap, tracker.accepted, request_count, tracker.reads, tracker.writes))
    end
    foreach (requests[index]) begin
      if (!check_response(requests[index])) passed = 1'b0;
      else if (is_write[index]) begin
        readback = linear_footprint(requests[index], 1'b0);
        issue_request(readback);
        if (check_response(readback)) compare_read(readback, requests[index]);
        else passed = 1'b0;
      end else if (seeded[index]) compare_read(requests[index], seeds[index]);
      else passed = 1'b0;
    end
    `uvm_info("USB_COMBO_RANDOM", $sformatf("%s requests=%0d, accepted read/write overlap verified, peak reads/writes=%0d/%0d; all requests completed", passed ? "PASS" : "FAIL response checks", request_count, max_reads, max_writes), UVM_LOW)
  endtask

  protected task run_backpressure();
    aaxi_master_tr requests[10], seeds[10], readback;
    bit seeded[10];
    aaxi_sequencer manager;
    usb_axi_inflight_callbacks tracker;
    int unsigned ids[6] = '{2, 3, 2, 4, 3, 2};
    // The first write's long BREADY hold backs up the write responses so every bridge FIFO fills;
    // the other holds stay short to keep the batch fast.
    int unsigned read_stall = 32, write_stall = 16, first_write_stall = 512;
    logic [31:0] offset;
    realtime clock_sample;
    time request_timeout;
    bit tracking, overlap, passed = 1'b1;

    if (p_sequencer.reg_model.combo.hub.DESCRIPTOR_HIGH.m_mem.get_size() < 160) begin
      `uvm_fatal("USB_COMBO_BACKPRESSURE", "Backpressure batch requires 160 contiguous Hub descriptor DWORDs")
    end
    foreach (requests[index]) begin
      offset = index == 2 ? 32'h40 : index == 6 ? 32'h100 : hub_high_offset + 64 * index;
      requests[index] = make_request($sformatf("backpressure-%0d", index), offset, index < 6, $urandom(), 16);
      requests[index].id = aaxi_id_t'(ids[index % 6]);
      if (index > 6) begin
        seeds[index] = make_request("Hub-read-seed", offset, 1'b1, $urandom(), 16);
        issue_request(seeds[index]);
        seeded[index] = check_response(seeds[index]);
      end
    end
    p_sequencer.cfg.wait_bus_negedge();
    clock_sample = $realtime;
    p_sequencer.cfg.wait_bus_negedge();
    request_timeout = transfer_timeout() + time'((4 * 16 * read_stall + first_write_stall + 5 * write_stall) * ($realtime - clock_sample));
    manager = sequencer_for(USB_DEV0_CSR);
    // The existing RAM observer checks accepted requests and per-ID completion order.
    tracker = usb_axi_inflight_callbacks::type_id::create("combo_overlap_tracker");
    manager.cfg.agent.add_callback(tracker);
    tracking = 1'b1;
    `uvm_info("USB_COMBO_BACKPRESSURE", $sformatf("6 writes + 4 reads, INCR-16, unmapped write[2]/read[6], unchanged VIP outstanding budgets=%0d/%0d; BREADY stall=%0d (first write %0d), initial/inter-beat RREADY stall=%0d cycles, timeout=%0t", manager.cfg.get_config_int("total_outstanding_depth"), manager.cfg.get_config_int("id_outstanding_depth"), write_stall, first_write_stall, read_stall, request_timeout), UVM_LOW)
    fork
      begin
        while (tracking) begin
          p_sequencer.cfg.wait_bus_negedge();
          if (tracker.reads > 0 && tracker.writes > 0) overlap = 1'b1;
        end
      end
      begin
        foreach (requests[index]) begin
          automatic int slot = index;
          if (index == 6) repeat (32) p_sequencer.cfg.wait_bus_negedge();
          fork
            issue_request(requests[slot], slot == 0 ? first_write_stall : slot < 6 ? write_stall : read_stall, request_timeout);
          join_none
          repeat (2) p_sequencer.cfg.wait_bus_negedge();
        end
        wait fork;
        p_sequencer.cfg.wait_bus_negedge();
        tracking = 1'b0;
      end
    join
    manager.cfg.agent.delete_callback(tracker);
    if (!overlap || tracker.accepted != 10 || tracker.reads != 0 || tracker.writes != 0 ||
        tracker.read_ids.size() != 4 || tracker.write_ids.size() != 6 ||
        !tracker.separated_read_id || !tracker.separated_write_id) begin
      `uvm_fatal("USB_COMBO_BACKPRESSURE", $sformatf("Missing overlap/order/completion coverage: overlap=%0b accepted=%0d pending=%0d/%0d ARIDs=%p AWIDs=%p", overlap, tracker.accepted, tracker.reads, tracker.writes, tracker.read_ids, tracker.write_ids))
    end
    foreach (requests[index]) begin
      if (index == 2 || index == 6) passed &= check_response(requests[index], COMBO_ERROR);
      else if (!check_response(requests[index])) passed = 1'b0;
      else if (index < 6) begin
        readback = make_request("Hub-write-readback", 32'(requests[index].addr - base_address), 1'b0, '0, 16);
        issue_request(readback);
        if (check_response(readback)) compare_read(readback, requests[index]);
        else passed = 1'b0;
      end else if (seeded[index]) compare_read(requests[index], seeds[index]);
      else passed = 1'b0;
    end
    `uvm_info("USB_COMBO_BACKPRESSURE", $sformatf("%s: accepted/completed all 10 requests, read/write overlap and separated same-ID order verified; ARIDs=%p AWIDs=%p", passed ? "PASS" : "FAIL response checks", tracker.read_ids, tracker.write_ids), UVM_LOW)
  endtask

  // Enable Combo filtering with every allowlist entry set to the test USER.
  protected task configure_combo_policy();
    usb_combo_filter_api_seq_t policy;

    policy = usb_combo_filter_api_seq_t::type_id::create("combo_policy");
    policy.op = USB_AXI_USER_FILTER_SET_POLICY;
    policy.enable = 1'b1;
    foreach (policy.priv_axi_users[index]) policy.priv_axi_users[index] = authorized_user.value;
    policy.start(p_sequencer.combo_filter_sequencer, this);
  endtask

  // Allow: every entry is the test USER. Deny: every entry is a different USER.
  protected virtual task set_allowlist(bit allow);
    usb_combo_filter_api_seq_t policy;

    policy = usb_combo_filter_api_seq_t::type_id::create("combo_allowlist");
    policy.op = USB_AXI_USER_FILTER_SET_USERS;
    foreach (policy.priv_axi_users[index]) policy.priv_axi_users[index] = allow ? authorized_user.value : authorized_user.value ^ usb_axi_user_t'(1);
    policy.start(p_sequencer.combo_filter_sequencer, this);
  endtask

  // The Hub must be disabled and disconnected before descriptor storage is modified.
  protected task check_hub_disabled(string label);
    aaxi_master_tr request;

    request = make_request(label, reg_offset(USB_HUB, p_sequencer.reg_model.combo.hub.CONTROL), 1'b0);
    issue_request(request);
    if (check_response(request)) begin
      if (request.data.size() != 4) `uvm_fatal("USB_COMBO_DATA", "Hub CONTROL did not return four bytes")
      if ((data_word(request, 0) & 32'h0001_0001) !== '0) `uvm_fatal("USB_COMBO_SETUP", "Hub must be disabled/disconnected before modifying descriptor storage")
    end
  endtask

  protected virtual task restore_policy();
    configure_combo_policy();
  endtask

  protected virtual function void count_checked(int unsigned words);
    checked_words += words;
  endfunction

  // The Hub must still be disabled, and every Combo region must work after reset.
  protected virtual task post_reset_checks(output bit passed);
    bit region_ok;

    check_hub_disabled("Hub-disabled-after-reset");
    passed = 1'b1;
    foreach (offsets[region]) begin
      write_read_word(region, $urandom(), region_ok);
      passed &= region_ok;
    end
  endtask

  task body();
    usb_axi_user_t axi_user;
    uvm_reg_map combo_map;
    bit passed;

    completed = 1'b0;
    // Hub storage shares the Combo manager and map with DEV0-CSR.
    bridge_target = USB_DEV0_CSR;
    bridge_name = "Combo Hub";
    tag_prefix = "USB_COMBO";
    launched = 0;
    finished = 0;
    checked_words = 0;
    positive_pairs = 0;
    expected_errors = 0;
    error_recoveries = 0;
    write_probes = 0;
    hazard_cases = 0;
    policy_cases = 0;
    reset_abandoned = 0;
    reset_passed = 1'b0;

    if (!std::randomize(axi_user)) `uvm_fatal("USB_COMBO_USER", "AXI USER randomization failed")
    
    authorized_user = usb_axi_user_override::with_value(axi_user);
    configure_combo_policy();
    
    combo_map = map_for(USB_DEV0_CSR);
    base_address = combo_map.get_base_addr(UVM_NO_HIER);
    offsets[0] = csr_offset(USB_DEV0_CSR, "INTROUTE");
    offsets[1] = reg_offset(USB_DEV0_CSR, p_sequencer.reg_model.combo.recovery.DEVICE_ID_1);
    offsets[2] = mem_word_offset(USB_HUB, p_sequencer.reg_model.combo.hub.DESCRIPTOR_LOW.m_mem, 2);
    hub_high_offset = mem_word_offset(USB_HUB, p_sequencer.reg_model.combo.hub.DESCRIPTOR_HIGH.m_mem, 0);
    
    // CaliptraSSHardwareSpecification: Combo AXI memory map, rounded Hub/window sizes.
    hub_end = 32'h1000 + (32'd4 << $clog2(USB_HUB_FIFO_SIZE));
    combo_bytes = 32'd1 << $clog2(hub_end);
    `uvm_info("USB_COMBO_SETUP", $sformatf("USER=0x%08h Combo base=0x%016h Hub aperture end=0x%08h Combo bytes=0x%08h", axi_user, base_address, hub_end, combo_bytes), UVM_LOW)

    //Issue single AXI read to check Hub control reg ENABLE/DCON bits
    check_hub_disabled("Hub-disabled-precondition");

    //Issue write/reads to different regions
    foreach (offsets[region]) write_read_word(region, $urandom(), passed);


    run_burst_cases();
    
    run_random_accesses();
    
    run_unmapped_cases();
    
    run_observations();
    
    //Write across region edges and outside the Combo window; observe side effects
    run_write_observations();
    
    run_backpressure();

    //Race reads and writes to the same Hub address and check AXI ordering rules
    run_same_address_hazards(hub_high_offset);

    // Flip the Combo allowlist while a request is in flight; it must keep its acceptance-time decision.
    run_policy_change_cases(hub_high_offset + 'h180);

    // Allowed-USER and denied-USER Hub requests in flight together; each keeps its own filter decision.
    run_mixed_user_batch(hub_high_offset);

    // Last: pulse the AXI reset with a read and a write outstanding.
    run_reset_with_outstanding(hub_high_offset, hub_high_offset + 'h40, hub_high_offset + 'h80);
    
    if (launched != finished + reset_abandoned) `uvm_fatal("USB_COMBO_RESPONSE", "Combo requests remain outstanding")
    `uvm_info("USB_COMBO_SUMMARY", $sformatf("Completed %0d/%0d requests (items unreturned after reset=%0d), %0d checked DWORDs, %0d single-word write/read pairs, %0d expected SLVERR/DECERR responses, %0d SLVERR/DECERR-to-OKAY recoveries, %0d crossing/outside-window write probes, hazard_cases=%0d/6, policy_cases=%0d/4, mixed_user=%s (%0d/%0d), reset=%s; OOB/narrow/outside-window/after-reset contents are observations, not added USB guarantees", finished, launched, reset_abandoned, checked_words, positive_pairs, expected_errors, error_recoveries, write_probes, hazard_cases, policy_cases, mixed_passed ? "PASS" : "FAIL", mixed_requests, MIXED_SLOTS, reset_passed ? "PASS" : "FAIL"), UVM_LOW)
    completed = 1'b1;
  endtask
endclass
