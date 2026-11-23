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

  // DEV1 response holds stay below the Axi4PC 16-cycle MAX_WAIT recommendation.
  localparam int unsigned DEV1_STALL = 15;
  localparam int unsigned TRANSITION_STEPS = 8;
  localparam int unsigned TRANSITION_UNMAPPED = 3;
  // 256 DWORDs from here end at 0x7FF: inside the 0x40-0x7FF Combo hole and one 4 KiB page.
  localparam logic [31:0] LONG_HOLE_OFFSET = 32'h400;
  localparam int unsigned AXI_MAX_INCR_BEATS = 256;

  protected logic [31:0] offsets[3];
  protected logic [31:0] masks[3] = '{USB_DEV0_ROUTE_MASK, '1, '1};
  protected string region_names[3] = '{"DEV0-CSR", "OCP-Recovery", "Hub"};
  protected logic [31:0] hub_end;
  protected logic [31:0] combo_bytes;
  protected logic [31:0] hub_high_offset;
  protected int unsigned checked_words, positive_pairs;
  protected int unsigned expected_errors, error_recoveries, write_probes;
  protected int unsigned dev1_requests, transition_requests;

  function new(string name = "usb_axi_combo_access_seq");
    super.new(name);
  endfunction

  // Build a request on the current bridge with any size, length, and burst type.
  // Write beats after the first get random data.
  protected function aaxi_master_tr make_request(string label, logic [31:0] offset, bit is_write, logic [31:0] first_word = '0, int unsigned beats = 1, int unsigned size = 2, combo_burst_e burst = COMBO_INCR);
    aaxi_master_tr request;
    logic [31:0] data;

    // Select the current bridge's manager without applying the per-target address guard.
    request = create_transaction(bridge_target, offset, is_write, first_word, authorized_user);
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

  // Check every response beat: OKAY, an error (SLVERR/DECERR), or just log it.
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

  // Build an INCR request that covers the same DWORDs as the given burst.
  protected function aaxi_master_tr linear_footprint(aaxi_master_tr request, bit is_write);
    uvm_reg_addr_t first;
    int unsigned words;

    burst_span(aaxi_burst_type'(request.burst), request.addr - base_address, int'(request.len) + 1, first, words);
    return make_request({request.get_name(), "-linear"}, 32'(first), is_write, is_write ? $urandom() : '0, words);
  endfunction

  // Check each read beat against the last write beat that hit the same address.
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

  // Write one masked DWORD at an offset on the current bridge, then read it back and compare.
  protected task write_read_offset(string label, logic [31:0] offset, logic [31:0] value, logic [31:0] mask, output bit passed);
    aaxi_master_tr written, readback;

    passed = 1'b0;
    written = make_request(label, offset, 1'b1, value & mask);
    issue_request(written);
    if (!check_response(written)) return;
    readback = make_request(label, offset, 1'b0);
    issue_request(readback);
    if (!check_response(readback)) return;
    compare_read(readback, written, mask);
    positive_pairs++;
    passed = 1'b1;
    `uvm_info("USB_COMBO_DATA", $sformatf("PASS %s AXI=0x%016h expected=0x%08h actual=0x%08h mask=0x%08h", label, readback.addr, data_word(written, 0), data_word(readback, 0), mask), UVM_LOW)
  endtask

  // Single-DWORD write/read of one Combo region's test register.
  protected task write_read_word(int unsigned region, logic [31:0] value, output bit passed);
    write_read_offset(region_names[region], offsets[region], value, masks[region], passed);
  endtask

  // Check every beat of a read that lands on offset against the expected masked value.
  protected function void check_word_at(aaxi_master_tr request, logic [31:0] offset, logic [31:0] expected, logic [31:0] mask);
    uvm_reg_addr_t address = base_address + offset;
    logic [31:0] actual;
    int unsigned hits = 0;

    if (request.data.size() != 4 * (int'(request.len) + 1)) begin
      `uvm_fatal("USB_COMBO_DATA", $sformatf("%s: returned %0d bytes for %0d beats", request.get_name(), request.data.size(), int'(request.len) + 1))
    end
    for (int unsigned beat = 0; beat <= int'(request.len); beat++) begin
      if (beat_address(request, beat) != address) continue;
      actual = data_word(request, beat) & mask;
      if (actual !== (expected & mask)) begin
        `uvm_fatal("USB_COMBO_DATA", $sformatf("%s AXI=0x%016h BURST=%0h beat=%0d expected=0x%08h actual=0x%08h mask=0x%08h", request.get_name(), address, request.burst, beat, expected & mask, actual, mask))
      end
      hits++;
      checked_words++;
    end
    if (hits == 0) `uvm_fatal("USB_COMBO_DATA", $sformatf("%s: no beat reached AXI=0x%016h", request.get_name(), address))
  endfunction

  // Write a burst, read it back with the same burst, and compare. WRAP bursts also
  // get a linear readback.
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

  // Run FIXED and WRAP bursts of several lengths, then the long INCR cases.
  protected task run_burst_cases();
    int unsigned fixed_lengths[3] = '{1, 2, 16};
    int unsigned wrap_lengths[4] = '{2, 4, 8, 16};

    foreach (fixed_lengths[index]) begin
      write_read_burst($sformatf("FIXED-%0d", fixed_lengths[index]), hub_high_offset, fixed_lengths[index], COMBO_FIXED);
    end
    foreach (wrap_lengths[index]) begin
      write_read_burst($sformatf("WRAP-%0d", wrap_lengths[index]), hub_high_offset + 4 * (wrap_lengths[index] - 1), wrap_lengths[index], COMBO_WRAP);
    end
    run_long_incr_cases();
  endtask

  // INCR bursts longer than 16 beats: all of Hub DESCRIPTOR_HIGH (data-checked), then
  // AxLEN=255 read and write in the unmapped hole (every R beat and the B must be an error).
  protected task run_long_incr_cases();
    int unsigned hub_beats = int'(p_sequencer.reg_model.combo.hub.DESCRIPTOR_HIGH.m_mem.get_size());
    aaxi_master_tr request;
    int unsigned nonzero_words;
    bit negative_ok = 1'b1;
    bit request_ok, positive_ok;

    if (hub_beats < 17 || hub_beats > AXI_MAX_INCR_BEATS || (hub_high_offset % 4096) + 4 * hub_beats > 4096) begin
      `uvm_fatal("USB_COMBO_BURST", $sformatf("Hub DESCRIPTOR_HIGH (%0d DWORDs at 0x%08h) is not a legal >16-beat INCR footprint", hub_beats, hub_high_offset))
    end
    write_read_burst($sformatf("Hub-INCR-%0d", hub_beats), hub_high_offset, hub_beats, COMBO_INCR);

    for (int unsigned direction = 0; direction < 2; direction++) begin
      string direction_name;

      if (direction == 1) direction_name = "write";
      else direction_name = "read";
      request = make_request($sformatf("unmapped-INCR-%0d-%s", AXI_MAX_INCR_BEATS, direction_name), LONG_HOLE_OFFSET, direction == 1, $urandom(), AXI_MAX_INCR_BEATS);
      issue_request(request);
      request_ok = check_response(request, COMBO_ERROR);
      if (!request_ok) negative_ok = 1'b0;
      if (direction == 0) begin
        // AXI defines no read data for error beats; record what came back.
        nonzero_words = 0;
        for (int unsigned beat = 0; beat <= int'(request.len); beat++) begin
          if (data_word(request, beat) !== '0) nonzero_words++;
        end
        `uvm_info("USB_COMBO_OBSERVE", $sformatf("%s AXI=0x%016h non-OKAY beat payload: %0d/%0d nonzero DWORDs", request.get_name(), request.addr, nonzero_words, AXI_MAX_INCR_BEATS), UVM_LOW)
      end
      `uvm_info("USB_COMBO_DECODE", $sformatf("%s AXI=0x%016h beats=%0d expected_SLVERR_or_DECERR=%0b", request.get_name(), request.addr, AXI_MAX_INCR_BEATS, request_ok), UVM_LOW)
    end
    write_read_word(0, $urandom(), positive_ok);
    if (negative_ok && positive_ok) error_recoveries++;
  endtask

  // Read and write unmapped Combo offsets and expect errors. After each one, check
  // that a normal access still works.
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

  // Back-to-back same-ID single-beat reads, then writes, that walk the Combo map in a fixed
  // order: DEV0-CSR, Recovery, Hub, Recovery, Unmapped, DEV0-CSR, Recovery, DEV0-CSR.
  // Same-ID requests complete in order (AXI A6.5), so the last write to each register wins.
  protected task run_region_transitions();
    int unsigned order[TRANSITION_STEPS] = '{0, 1, 2, 1, TRANSITION_UNMAPPED, 0, 1, 0};
    logic [31:0] step_offsets[TRANSITION_STEPS];
    logic [31:0] step_data[TRANSITION_STEPS];
    logic [31:0] expected[3];
    aaxi_master_tr requests[TRANSITION_STEPS], readback;
    uvm_reg_addr_t history[$];
    string tag = {tag_prefix, "_TRANSITION"};
    bit is_write, seeded;

    foreach (order[step]) step_offsets[step] = order[step] == TRANSITION_UNMAPPED ? 32'h40 : offsets[order[step]];
    foreach (offsets[region]) begin
      expected[region] = $urandom() & masks[region];
      write_read_word(region, expected[region], seeded);
      if (!seeded) `uvm_fatal(tag, $sformatf("%s seed write/read failed", region_names[region]))
    end
    for (int unsigned pass = 0; pass < 2; pass++) begin
      is_write = pass == 1;
      foreach (requests[step]) begin
        step_data[step] = $urandom();
        if (is_write && order[step] != TRANSITION_UNMAPPED) begin
          step_data[step] &= masks[order[step]];
          expected[order[step]] = step_data[step];
        end
        requests[step] = make_request($sformatf("transition-%s-%0d", is_write ? "write" : "read", step), step_offsets[step], is_write, step_data[step]);
      end
      start_inflight_tracker(is_write ? "combo_transition_writes" : "combo_transition_reads", 0);
      // Queue every request at once with no response stalls so AHB address phases chain.
      // Bus order relies on join_none children starting in fork order: VCS does this, but IEEE 1800
      // leaves it unspecified. The address check below misses a swap of two same-address steps.
      foreach (requests[step]) begin
        automatic int slot = step;
        fork
          issue_request(requests[slot], 0, inflight_timeout);
        join_none
      end
      wait fork;
      stop_inflight_tracker(tag);
      transition_requests += TRANSITION_STEPS;
      history = is_write ? inflight_tracker.write_history : inflight_tracker.read_history;
      if (history.size() != TRANSITION_STEPS) begin
        `uvm_fatal(tag, $sformatf("%0d/%0d %s addresses accepted", history.size(), TRANSITION_STEPS, is_write ? "write" : "read"))
      end
      foreach (requests[step]) begin
        if (history[step] != requests[step].addr) begin
          `uvm_fatal(tag, $sformatf("TB issue order differs at step %0d: expected AXI=0x%016h accepted=0x%016h", step, requests[step].addr, history[step]))
        end
      end
      foreach (requests[step]) begin
        if (order[step] == TRANSITION_UNMAPPED) void'(check_response(requests[step], COMBO_ERROR));
        else if (check_response(requests[step]) && !is_write) begin
          check_word_at(requests[step], step_offsets[step], expected[order[step]], masks[order[step]]);
        end
      end
      `uvm_info(tag, $sformatf("%s pass: %0d back-to-back requests accepted in order %p", is_write ? "Write" : "Read", TRANSITION_STEPS, order), UVM_LOW)
    end
    foreach (offsets[region]) begin
      readback = make_request($sformatf("%s-after-transitions", region_names[region]), offsets[region], 1'b0);
      issue_request(readback);
      if (check_response(readback)) check_word_at(readback, offsets[region], expected[region], masks[region]);
    end
  endtask

  // Check that reads crossing into unmapped space get an error there. Log, without
  // checking, an outside-window read and byte/halfword accesses.
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

  // Send 2-10 random reads and writes at once with random bursts. Check that reads
  // and writes overlapped, then check all responses and data.
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

  // Send 6 writes and 4 reads with slow responses so the bridge queues fill. Check
  // errors on the unmapped ones, same-ID order, and data.
  protected task run_backpressure();
    aaxi_master_tr requests[10], seeds[10], readback;
    bit seeded[10];
    aaxi_sequencer manager;
    usb_axi_inflight_callbacks tracker;
    aaxi_id_t ids[6];
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
    separated_id_pattern(ids);
    foreach (requests[index]) begin
      offset = index == 2 ? 32'h40 : index == 6 ? 32'h100 : hub_high_offset + 64 * index;
      requests[index] = make_request($sformatf("backpressure-%0d", index), offset, index < 6, $urandom(), 16);
      requests[index].id = ids[index % 6];
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

  // Enable the DEV1 filter with every allowlist entry set to the test USER.
  protected task configure_dev1_policy();
    usb_dev1_filter_api_seq_t policy;

    policy = usb_dev1_filter_api_seq_t::type_id::create("dev1_policy");
    policy.op = USB_AXI_USER_FILTER_SET_POLICY;
    policy.enable = 1'b1;
    foreach (policy.priv_axi_users[index]) policy.priv_axi_users[index] = authorized_user.value;
    policy.start(p_sequencer.dev1_filter_sequencer, this);
  endtask

  // Legal DWORD traffic on the DEV1 CSR bridge: singles, INCR/FIXED/WRAP bursts, and a
  // concurrent multi-ID batch with short response holds. Only the RW INTEN/INTROUTE
  // registers change; W1C INTSTAT and W1S INTSETSTAT are written with zero (no effect).
  protected task run_dev1_csr_accesses();
    usb_target_e saved_target = bridge_target;
    string saved_name = bridge_name;
    uvm_reg_addr_t saved_base = base_address;
    int unsigned first_launched = launched;
    // INTEN shares INTROUTE's EP/FRAME/DEV field layout (RAL).
    logic [31:0] mask = USB_DEV1_ROUTE_MASK;
    logic [31:0] inten, introute, intstat, intsetstat, offset, route_value, enable_value;
    logic [31:0] words[], batch_offsets[6];
    aaxi_master_tr request, readback, writes[6], reads[2];
    aaxi_id_t ids[6];
    int unsigned beats;
    string tag = {tag_prefix, "_DEV1"};
    bit passed;

    bridge_target = USB_DEV1_CSR;
    bridge_name = "DEV1 CSR";
    base_address = map_for(USB_DEV1_CSR).get_base_addr(UVM_NO_HIER);
    configure_dev1_policy();
    intstat = csr_offset(USB_DEV1_CSR, "INTSTAT");
    inten = csr_offset(USB_DEV1_CSR, "INTEN");
    intsetstat = csr_offset(USB_DEV1_CSR, "INTSETSTAT");
    introute = csr_offset(USB_DEV1_CSR, "INTROUTE");
    beats = csr_offset(USB_DEV1_CSR, "EPTOGGLE") / 4 + 1;
    if (intstat % 16 != 0 || inten != intstat + 4 || intsetstat != intstat + 8 || introute != intstat + 12) begin
      `uvm_fatal(tag, "WRAP-4 window must hold INTSTAT, INTEN, INTSETSTAT, INTROUTE in order")
    end

    route_value = $urandom() & mask;
    write_read_offset("DEV1-INTROUTE", introute, route_value, mask, passed);
    enable_value = $urandom() & mask;
    write_read_offset("DEV1-INTEN", inten, enable_value, mask, passed);

    readback = make_request("DEV1-INCR-read", '0, 1'b0, '0, beats);
    issue_request(readback);
    if (check_response(readback)) begin
      check_word_at(readback, introute, route_value, mask);
      check_word_at(readback, inten, enable_value, mask);
    end

    // FIXED: the last write beat wins.
    request = make_request("DEV1-FIXED-write", introute, 1'b1, $urandom(), 4, 2, COMBO_FIXED);
    issue_request(request);
    if (check_response(request)) begin
      route_value = data_word(request, 3) & mask;
      readback = make_request("DEV1-FIXED-read", introute, 1'b0, '0, 4, 2, COMBO_FIXED);
      issue_request(readback);
      if (check_response(readback)) compare_read(readback, request, mask);
    end

    // WRAP-4 from INTROUTE visits INTROUTE, INTSTAT, INTEN, INTSETSTAT.
    route_value = $urandom() & mask;
    enable_value = $urandom() & mask;
    request = make_request("DEV1-WRAP-write", introute, 1'b1, '0, 4, 2, COMBO_WRAP);
    words = new[4];
    foreach (words[beat]) begin
      offset = 32'(beat_address(request, beat) - base_address);
      words[beat] = offset == introute ? route_value : offset == inten ? enable_value : '0;
    end
    set_write_words(request, words);
    issue_request(request);
    if (check_response(request)) begin
      readback = make_request("DEV1-WRAP-read", introute, 1'b0, '0, 4, 2, COMBO_WRAP);
      issue_request(readback);
      if (check_response(readback)) begin
        check_word_at(readback, introute, route_value, mask);
        check_word_at(readback, inten, enable_value, mask);
      end
    end

    // Six writes with IDs A,B,A,C,B,A, then two reads (B, A); every response is held
    // DEV1_STALL cycles so the response FIFOs fill.
    separated_id_pattern(ids);
    route_value = $urandom() & mask;
    enable_value = $urandom() & mask;
    batch_offsets = '{introute, inten, intsetstat, intstat, intsetstat, intstat};
    foreach (writes[index]) begin
      writes[index] = make_request($sformatf("DEV1-batch-write-%0d", index), batch_offsets[index], 1'b1, index == 0 ? route_value : index == 1 ? enable_value : '0);
      writes[index].id = ids[index];
    end
    foreach (reads[index]) begin
      reads[index] = make_request($sformatf("DEV1-batch-read-%0d", index), '0, 1'b0, '0, beats);
      reads[index].id = ids[index + 1];
    end
    start_inflight_tracker("dev1_csr_tracker", ($size(writes) + $size(reads) * beats) * DEV1_STALL);
    foreach (writes[index]) begin
      automatic int slot = index;
      fork
        issue_request(writes[slot], DEV1_STALL, inflight_timeout);
      join_none
    end
    wait fork;
    foreach (reads[index]) begin
      automatic int slot = index;
      fork
        issue_request(reads[slot], DEV1_STALL, inflight_timeout, 0, 1'b0);
      join_none
    end
    wait fork;
    stop_inflight_tracker(tag);
    if (inflight_tracker.accepted != $size(writes) + $size(reads)) begin
      `uvm_fatal(tag, $sformatf("Accepted %0d/%0d batch requests", inflight_tracker.accepted, $size(writes) + $size(reads)))
    end
    foreach (writes[index]) void'(check_response(writes[index]));
    foreach (reads[index]) begin
      if (check_response(reads[index])) begin
        check_word_at(reads[index], introute, route_value, mask);
        check_word_at(reads[index], inten, enable_value, mask);
      end
    end
    `uvm_info(tag, $sformatf("Batch AWIDs=%p ARIDs=%p separated same-ID writes=%0b", inflight_tracker.write_ids, inflight_tracker.read_ids, inflight_tracker.separated_write_id), UVM_LOW)

    write_read_offset("DEV1-INTEN-restore", inten, '0, mask, passed);
    write_read_offset("DEV1-INTROUTE-restore", introute, '0, mask, passed);
    dev1_requests = launched - first_launched;
    bridge_target = saved_target;
    bridge_name = saved_name;
    base_address = saved_base;
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

  // Put back the Combo filter policy the normal tests use.
  protected virtual task restore_policy();
    configure_combo_policy();
  endtask

  // Add to the checked-word count.
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
    dev1_requests = 0;
    transition_requests = 0;
    hazard_cases = 0;
    policy_cases = 0;
    reset_abandoned = 0;
    reset_passed = 1'b0;

    if (!std::randomize(axi_user)) `uvm_fatal("USB_COMBO_USER", "AXI USER randomization failed")
    
    authorized_user = usb_axi_user_override::with_value(axi_user);
    randomize_manager_ids();
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

    // Back-to-back requests that move the Combo decoder between regions, including Unmapped.
    run_region_transitions();
    
    run_observations();
    
    //Write across region edges and outside the Combo window; observe side effects
    run_write_observations();
    
    run_backpressure();

    // Legal DWORD singles, bursts and a concurrent batch on the DEV1 CSR bridge.
    run_dev1_csr_accesses();

    //Race reads and writes to the same Hub address and check AXI ordering rules
    run_same_address_hazards(hub_high_offset);

    // Flip the Combo allowlist while a request is in flight; it must keep its acceptance-time decision.
    run_policy_change_cases(hub_high_offset + 'h180);

    // Allowed-USER and denied-USER Hub requests in flight together; each keeps its own filter decision.
    run_mixed_user_batch(hub_high_offset);

    // Last: pulse the AXI reset with a read and a write outstanding.
    run_reset_with_outstanding(hub_high_offset, hub_high_offset + 'h40, hub_high_offset + 'h80);
    
    if (launched != finished + reset_abandoned) `uvm_fatal("USB_COMBO_RESPONSE", "Combo requests remain outstanding")
    `uvm_info("USB_COMBO_SUMMARY", $sformatf("Completed %0d/%0d requests (items unreturned after reset=%0d), %0d checked DWORDs, %0d single-word write/read pairs, %0d expected SLVERR/DECERR responses, %0d SLVERR/DECERR-to-OKAY recoveries, %0d crossing/outside-window write probes, region-transition requests=%0d, DEV1 CSR requests=%0d, hazard_cases=%0d/6, policy_cases=%0d/4, mixed_user=%s (%0d/%0d), reset=%s; OOB/narrow/outside-window/after-reset contents are observations, not added USB guarantees", finished, launched, reset_abandoned, checked_words, positive_pairs, expected_errors, error_recoveries, write_probes, transition_requests, dev1_requests, hazard_cases, policy_cases, mixed_passed ? "PASS" : "FAIL", mixed_requests, MIXED_SLOTS, reset_passed ? "PASS" : "FAIL"), UVM_LOW)
    completed = 1'b1;
  endtask
endclass
