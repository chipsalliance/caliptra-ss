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
class usb_axi_dev_ram_rw_seq extends usb_axi_bridge_base_seq;
  `uvm_object_utils(usb_axi_dev_ram_rw_seq)

  localparam logic [31:0] TEST_OFFSET = 32'h0000_1000;

  typedef enum {RAM_FIXED, RAM_INCR, RAM_WRAP} ram_burst_e;
  typedef struct {
    string label;
    ram_burst_e burst;
    uvm_reg_addr_t offset;
    int unsigned beats;
    aaxi_id_t id;
    logic [31:0] write_data[];
  } ram_case_t;

  protected usb_target_e ram_target;
  protected logic [31:0] ram_bytes;
  protected logic [31:0] expected_words[int unsigned];
  protected int unsigned positive_cases;
  protected int unsigned checked_beats;
  protected int unsigned max_reads;
  protected int unsigned max_writes;
  protected bit read_write_overlap;

  function new(string name = "usb_axi_dev_ram_rw_seq");
    super.new(name);
  endfunction

  // Build a RAM test case that uses the target's default ID.
  protected function ram_case_t make_case(string label, ram_burst_e burst, uvm_reg_addr_t offset, int unsigned beats);
    ram_case_t c;

    c.label = label;
    c.burst = burst;
    c.offset = offset;
    c.beats = beats;
    c.id = transaction_id_for(ram_target);
    c.write_data = new[0];
    return c;
  endfunction

  // Convert the local burst type to the Avery burst type.
  protected function aaxi_burst_type axi_burst(ram_burst_e burst);
    case (burst)
      RAM_FIXED: return AAXI_BURST_FIXED;
      RAM_WRAP:  return AAXI_BURST_WRAP;
      default:   return AAXI_BURST_INCR;
    endcase
  endfunction

  // RAM offset of one beat of a case.
  protected function uvm_reg_addr_t beat_offset(ram_case_t c, int unsigned beat);
    return burst_beat_address(axi_burst(c.burst), c.offset, c.beats, beat);
  endfunction

  // Send a case as a read or write. Writes without data get random words that
  // differ from what is already stored.
  protected task send_ram_request(inout ram_case_t c, input bit is_write, output aaxi_master_tr request, input int unsigned response_stall = 0, input time request_timeout = 0, input bit stall_each_read_beat = 0, input int unsigned write_data_delay = 0);
    int unsigned word;

    request = create_transaction(ram_target, 32'(c.offset), is_write, '0, authorized_user);
    request.set_name(c.label);
    request.id = c.id;
    request.len = c.beats - 1;
    request.burst = axi_burst(c.burst);
    request.wuser_A = new[c.beats];
    foreach (request.wuser_A[beat]) request.wuser_A[beat] = authorized_user.value;

    if (is_write) begin
      if (c.write_data.size() == 0) begin
        c.write_data = new[c.beats];
        foreach (c.write_data[beat]) begin
          word = int'(beat_offset(c, beat));
          c.write_data[beat] = $urandom();
          // Make rewrites distinguishable from the stored value.
          if (expected_words.exists(word) && c.write_data[beat] === expected_words[word]) begin
            c.write_data[beat] ^= 32'h0000_0001;
          end
        end
      end
      if (c.write_data.size() != c.beats) begin
        `uvm_fatal("USB_DEV0_RAM_DATA", $sformatf("%s: write payload has %0d words for %0d beats", c.label, c.write_data.size(), c.beats))
      end
      set_write_words(request, c.write_data);
    end
    issue_request(request, response_stall, request_timeout, write_data_delay, stall_each_read_beat);
  endtask

  // Check that a write returned OKAY and record its words as expected. On an error,
  // mark those words unknown.
  protected function bit check_write(aaxi_master_tr request, ram_case_t c);
    if (request.resp !== AAXI_RESP_OKAY) begin
      `uvm_error("USB_DEV0_RAM_RESPONSE", $sformatf("%s %s write AXI=0x%016h USER=0x%0h SIZE=%0d beats=%0d expected_resp=%0h actual_resp=%0h", c.label, c.burst.name(), request.addr, request.awuser, request.size, c.beats, AAXI_RESP_OKAY, request.resp))
      // An error response does not guarantee that no write beats took effect.
      for (int unsigned beat = 0; beat < c.beats; beat++) begin
        expected_words[int'(beat_offset(c, beat))] = 'x;
      end
      return 1'b0;
    end
    for (int unsigned beat = 0; beat < c.beats; beat++) begin
      expected_words[int'(beat_offset(c, beat))] = c.write_data[beat];
    end
    target_stats[ram_target].writes++;
    return 1'b1;
  endfunction

  // Check that a read returned OKAY on every beat and that its data matches the
  // expected words.
  protected function bit check_read(aaxi_master_tr request, ram_case_t c);
    logic [31:0] actual;
    logic [31:0] expected;
    int unsigned word;
    bit passed = 1'b1;

    if (request.rresp_Q.size() != c.beats || request.data.size() != c.beats * 4) begin
      `uvm_fatal("USB_DEV0_RAM_RESPONSE", $sformatf("%s %s read AXI=0x%016h USER=0x%0h SIZE=%0d returned %0d responses/%0d bytes for %0d beats", c.label, c.burst.name(), request.addr, request.aruser, request.size, request.rresp_Q.size(), request.data.size(), c.beats))
    end

    for (int unsigned beat = 0; beat < c.beats; beat++) begin
      if (request.rresp_Q[beat] !== AAXI_RESP_OKAY) begin
        word = int'(beat_offset(c, beat));
        `uvm_error("USB_DEV0_RAM_RESPONSE", $sformatf("%s %s read beat=%0d/%0d offset=0x%08h AXI=0x%016h USER=0x%0h SIZE=%0d expected_resp=%0h actual_resp=%0h", c.label, c.burst.name(), beat, c.beats, word, base_address + word, request.aruser, request.size, AAXI_RESP_OKAY, request.rresp_Q[beat]))
        return 1'b0;
      end
    end

    for (int unsigned beat = 0; beat < c.beats; beat++) begin
      word = int'(beat_offset(c, beat));
      if (!expected_words.exists(word)) begin
        `uvm_fatal("USB_DEV0_RAM_DATA", $sformatf("%s: no initialized expected value at offset=0x%08h", c.label, word))
      end
      expected = expected_words[word];
      if ($isunknown(expected)) begin
        passed = 1'b0;
        continue;
      end
      for (int unsigned lane = 0; lane < 4; lane++) begin
        actual[lane * 8 +: 8] = request.data[beat * 4 + lane];
      end
      if (actual !== expected) begin
        `uvm_fatal("USB_DEV0_RAM_DATA", $sformatf("%s %s read beat=%0d/%0d offset=0x%08h AXI=0x%016h USER=0x%0h SIZE=%0d expected=0x%08h actual=0x%08h", c.label, c.burst.name(), beat, c.beats, word, base_address + word, request.aruser, request.size, expected, actual))
      end
      checked_beats++;
      target_stats[ram_target].comparisons++;
    end

    if (passed) target_stats[ram_target].reads++;
    return passed;
  endfunction

  // Build an INCR case that covers the same words as the given case.
  protected function ram_case_t footprint(ram_case_t c);
    uvm_reg_addr_t first;
    int unsigned words;

    burst_span(axi_burst(c.burst), c.offset, c.beats, first, words);
    return make_case({c.label, "-footprint"}, RAM_INCR, first, words);
  endfunction

  // Write a case, read it back, and compare. WRAP cases also get a linear readback.
  protected task write_read_ram(ram_case_t c);
    ram_case_t span;
    aaxi_master_tr request;

    send_ram_request(c, 1'b1, request);
    if (!check_write(request, c)) return;
    // An ordered read after WRAP writes prevents matching address bugs from canceling.
    if (c.burst == RAM_WRAP) begin
      span = footprint(c);
      send_ram_request(span, 1'b0, request);
      if (!check_read(request, span)) return;
    end
    send_ram_request(c, 1'b0, request);
    if (!check_read(request, c)) return;
    positive_cases++;
    `uvm_info("USB_DEV0_RAM_CASE", $sformatf("PASS %s %s %s offset=0x%08h beats=%0d USER=0x%0h", usb_target_name(ram_target), c.label, c.burst.name(), c.offset, c.beats, authorized_user.value), UVM_LOW)
  endtask

  // Enable both AXI filters with every allowlist entry set to the test USER.
  protected task configure_ram_policies();
    usb_combo_allowlist_t combo_users;
    usb_dev1_allowlist_t dev1_users;

    foreach (combo_users[index]) combo_users[index] = authorized_user.value;
    foreach (dev1_users[index]) dev1_users[index] = authorized_user.value;
    set_axi_user_filter_policies(1'b1, combo_users, 1'b1, dev1_users);
  endtask

  // Single-DWORD writes and reads, with other accesses between a write and its
  // readback.
  protected task run_single_beat_cases();
    ram_case_t c;
    ram_case_t earlier;
    ram_case_t other;
    aaxi_master_tr request;
    bit passed = 1'b1;

    write_read_ram(make_case("authorized", RAM_INCR, TEST_OFFSET, 1));

    c = make_case("interleaved-single", RAM_INCR, TEST_OFFSET + 32'h40, 1);
    send_ram_request(c, 1'b1, request);
    passed &= check_write(request, c);
    earlier = make_case("read-earlier-word", RAM_INCR, TEST_OFFSET, 1);
    send_ram_request(earlier, 1'b0, request);
    passed &= check_read(request, earlier);

    other = make_case("write-other-word", RAM_INCR, TEST_OFFSET + 32'h80, 1);
    send_ram_request(other, 1'b1, request);
    passed &= check_write(request, other);
    send_ram_request(c, 1'b0, request);
    passed &= check_read(request, c);
    other.label = "read-other-word";
    send_ram_request(other, 1'b0, request);
    passed &= check_read(request, other);
    if (passed) positive_cases++;
  endtask

  // Write and read back FIXED, INCR, and WRAP bursts of several lengths.
  protected task run_burst_cases();
    int unsigned fixed_lengths[3] = '{1, 2, 16};
    int unsigned incr_lengths[5] = '{1, 2, 4, 16, 256};
    int unsigned wrap_lengths[4] = '{2, 4, 8, 16};

    foreach (fixed_lengths[index]) begin
      write_read_ram(make_case($sformatf("FIXED-%0d", fixed_lengths[index]), RAM_FIXED, 'h2100, fixed_lengths[index]));
    end
    foreach (incr_lengths[index]) begin
      write_read_ram(make_case($sformatf("INCR-%0d", incr_lengths[index]), RAM_INCR, 'h2400, incr_lengths[index]));
    end
    foreach (wrap_lengths[index]) begin
      write_read_ram(make_case($sformatf("WRAP-%0d", wrap_lengths[index]), RAM_WRAP, 'h2800 + 4 * (wrap_lengths[index] - 1), wrap_lengths[index]));
    end
  endtask

  // Send 1-16 random reads and writes at once with slow responses. Check that
  // reads and writes overlapped, then check all data.
  protected task run_overlapping_accesses();
    ram_case_t cases[];
    ram_case_t span;
    ram_burst_e burst;
    uvm_reg_addr_t offset;
    int unsigned request_count;
    int unsigned beats;
    int unsigned response_stall = 1024;
    realtime clock_sample;
    time request_timeout;
    bit is_write[];
    bit write_choice;
    aaxi_master_tr requests[];
    aaxi_master_tr readback;
    aaxi_sequencer manager_sequencer;
    aaxi_agent manager;
    usb_axi_inflight_callbacks tracker;
    bit tracking;
    bit passed = 1'b1;

    if (!std::randomize(request_count) with {
      request_count inside {[1:16]};
    }) begin
      `uvm_fatal("USB_DEV0_RAM_RANDOM", "Request-count randomization failed")
    end
    cases = new[request_count];
    requests = new[request_count];
    is_write = new[request_count];
    foreach (cases[index]) begin
      if (!std::randomize(burst, beats, write_choice) with {
        burst inside {RAM_FIXED, RAM_INCR, RAM_WRAP};
        solve burst before beats;
        if (burst == RAM_FIXED) beats inside {[1:16]};
        if (burst == RAM_INCR)  beats inside {[1:256]};
        if (burst == RAM_WRAP)  beats inside {2, 4, 8, 16};
        if (index == 1) write_choice != is_write[0];
      }) begin
        `uvm_fatal("USB_DEV0_RAM_RANDOM", $sformatf("Request %0d randomization failed", index))
      end
      // Disjoint 1-KiB slots fit even INCR-256 without crossing a 4-KiB boundary.
      offset = uvm_reg_addr_t'(index) * 1024;
      if (burst == RAM_WRAP) offset += 4 * (beats - 1);
      cases[index] = make_case($sformatf("overlap-%0d", index), burst, offset, beats);
      is_write[index] = write_choice;
      `uvm_info("USB_DEV0_RAM_OVERLAP", $sformatf("%s write=%0b %s offset=0x%08h beats=%0d", cases[index].label, is_write[index], burst.name(), offset, beats), UVM_LOW)
      if (!is_write[index]) begin
        span = footprint(cases[index]);
        send_ram_request(span, 1'b1, requests[index]);
        void'(check_write(requests[index], span));
      end
    end
    manager_sequencer = sequencer_for(ram_target);
    manager = manager_sequencer.cfg.agent;
    if (manager == null) `uvm_fatal("USB_DEV0_RAM_OVERLAP", $sformatf("%s Avery manager is missing", usb_target_name(ram_target)))
    tracker = usb_axi_inflight_callbacks::type_id::create("ram_overlap_tracker");
    p_sequencer.cfg.wait_bus_negedge();
    clock_sample = $realtime;
    p_sequencer.cfg.wait_bus_negedge();
    // Budget for response stalls even if every request waits in series.
    request_timeout = transfer_timeout() + time'(request_count * response_stall * ($realtime - clock_sample));
    manager.add_callback(tracker);
    tracking = 1'b1;
    `uvm_info("USB_DEV0_RAM_BACKPRESSURE", $sformatf("Launching %0d requests: BREADY delay after BVALID=%0d cycles, initial RREADY delay after AR=%0d cycles, timeout=%0t", request_count, response_stall, response_stall, request_timeout), UVM_LOW)
    fork
      begin
        while (tracking) begin
          p_sequencer.cfg.wait_bus_negedge();
          if (tracker.reads > max_reads) max_reads = tracker.reads;
          if (tracker.writes > max_writes) max_writes = tracker.writes;
          if (tracker.reads > 0 && tracker.writes > 0) read_write_overlap = 1'b1;
        end
      end
      begin
        // Hold response readiness low so pressure can propagate toward AW/AR.
        foreach (cases[index]) begin
          automatic int slot = index;
          fork
            send_ram_request(cases[slot], is_write[slot], requests[slot], response_stall, request_timeout);
          join_none
        end
        wait fork;
        p_sequencer.cfg.wait_bus_negedge();
        tracking = 1'b0;
      end
    join
    manager.delete_callback(tracker);
    if ((request_count > 1 && !read_write_overlap) || tracker.accepted != request_count ||
        tracker.reads != 0 || tracker.writes != 0) begin
      `uvm_fatal("USB_DEV0_RAM_OVERLAP", $sformatf("Overlap=%0b accepted=%0d/%0d pending reads=%0d writes=%0d max_reads=%0d max_writes=%0d", read_write_overlap, tracker.accepted, request_count, tracker.reads, tracker.writes, max_reads, max_writes))
    end
    foreach (requests[index]) begin
      if (!is_write[index]) passed &= check_read(requests[index], cases[index]);
      else if (check_write(requests[index], cases[index])) begin
        span = footprint(cases[index]);
        send_ram_request(span, 1'b0, readback);
        passed &= check_read(readback, span);
      end else passed = 1'b0;
    end
    if (passed) positive_cases++;
    `uvm_info("USB_DEV0_RAM_OVERLAP", $sformatf("%s %s requests=%0d response_stall=%0d cycles overlap=%0s max_reads=%0d max_writes=%0d; all requests completed", passed ? "PASS" : "FAIL", usb_target_name(ram_target), request_count, response_stall, read_write_overlap ? "verified" : "N/A (single request)", max_reads, max_writes), UVM_LOW)
  endtask

  // Write and read back the first and last words of the RAM.
  protected task run_boundary_cases();
    write_read_ram(make_case("first-DWORD", RAM_INCR, 0, 1));
    write_read_ram(make_case("last-DWORD", RAM_INCR, ram_bytes - 4, 1));
    write_read_ram(make_case("last-FIXED", RAM_FIXED, ram_bytes - 4, 16));
    write_read_ram(make_case("last-INCR", RAM_INCR, ram_bytes - 64, 16));
    write_read_ram(make_case("last-WRAP", RAM_WRAP, ram_bytes - 4, 16));
  endtask

  // Send 6 writes and 4 reads with slow responses so the bridge queues fill. Check
  // same-ID order and data.
  protected task run_fifo_saturation();
    ram_case_t cases[10];
    aaxi_master_tr requests[10];
    aaxi_master_tr readback;
    aaxi_sequencer manager_sequencer;
    usb_axi_inflight_callbacks tracker;
    aaxi_id_t ids[6];
    // The first write's long BREADY hold backs up the write responses so every bridge FIFO fills;
    // the other holds stay short to keep the batch fast.
    int unsigned read_stall = 32;
    int unsigned write_stall = 16;
    int unsigned first_write_stall = 512;
    realtime clock_sample;
    time request_timeout;
    bit passed = 1'b1;

    separated_id_pattern(ids);
    foreach (cases[index]) begin
      cases[index] = make_case($sformatf("fifo-%0d", index), RAM_INCR, 'h6000 + 64 * index, 16);
      cases[index].id = ids[index % 6];
      `uvm_info("USB_DEV0_RAM_SATURATION", $sformatf("%s write=%0b RAM_INCR offset=0x%08h beats=16 ID=%0d", cases[index].label, index < 6, cases[index].offset, cases[index].id), UVM_LOW)
      if (index >= 6) begin
        send_ram_request(cases[index], 1'b1, requests[index]);
        void'(check_write(requests[index], cases[index]));
      end
    end
    p_sequencer.cfg.wait_bus_negedge();
    clock_sample = $realtime;
    p_sequencer.cfg.wait_bus_negedge();
    request_timeout = transfer_timeout() + time'((4 * 16 * read_stall + first_write_stall + 5 * write_stall) * ($realtime - clock_sample));
    manager_sequencer = sequencer_for(ram_target);
    tracker = usb_axi_inflight_callbacks::type_id::create("ram_id_tracker");
    manager_sequencer.cfg.agent.add_callback(tracker);
    `uvm_info("USB_DEV0_RAM_SATURATION", $sformatf("Launching 4 reads and 6 writes, INCR-16, unchanged VIP total/per-ID outstanding budgets=%0d/%0d, BREADY delay=%0d cycles (first write %0d), initial/inter-beat RREADY delays=%0d cycles, timeout=%0t", manager_sequencer.cfg.get_config_int("total_outstanding_depth"), manager_sequencer.cfg.get_config_int("id_outstanding_depth"), write_stall, first_write_stall, read_stall, request_timeout), UVM_LOW)
    foreach (cases[index]) begin
      automatic int slot = index;
      // Let write responses accumulate before adding read backpressure.
      if (index == 6) repeat (32) p_sequencer.cfg.wait_bus_negedge();
      fork
        send_ram_request(cases[slot], slot < 6, requests[slot], slot == 0 ? first_write_stall : slot < 6 ? write_stall : read_stall, request_timeout, 1'b1);
      join_none
      repeat (2) p_sequencer.cfg.wait_bus_negedge();
    end
    wait fork;
    manager_sequencer.cfg.agent.delete_callback(tracker);
    if (tracker.accepted != 10 || tracker.reads != 0 || tracker.writes != 0 ||
        tracker.read_ids.size() != 4 || tracker.write_ids.size() != 6 ||
        !tracker.separated_read_id || !tracker.separated_write_id) begin
      `uvm_fatal("USB_DEV0_RAM_ORDER", "Did not complete all requests with separated same-ID reads and writes outstanding together")
    end
    foreach (ids[index]) begin
      if (tracker.write_ids[index] != ids[index] ||
          (index < 4 && tracker.read_ids[index] != ids[index])) begin
        `uvm_fatal("USB_DEV0_RAM_ORDER", $sformatf("Unexpected accepted ID sequence: AR=%p AW=%p", tracker.read_ids, tracker.write_ids))
      end
    end
    `uvm_info("USB_DEV0_RAM_ORDER", $sformatf("PASS %s same-ID completion order; separated repeats outstanding; accepted ARIDs=%p AWIDs=%p", usb_target_name(ram_target), tracker.read_ids, tracker.write_ids), UVM_LOW)
    foreach (requests[index]) begin
      if (index >= 6) passed &= check_read(requests[index], cases[index]);
      else if (check_write(requests[index], cases[index])) begin
        send_ram_request(cases[index], 1'b0, readback);
        passed &= check_read(readback, cases[index]);
      end else passed = 1'b0;
    end
    if (passed) positive_cases++;
    `uvm_info("USB_DEV0_RAM_SATURATION", $sformatf("%s: %s", usb_target_name(ram_target), passed ? "PASS all 10 requests completed OKAY; all read data and write readbacks matched" : "FAIL response/data checks in 10-request batch"), UVM_LOW)
  endtask

  // Deny only the RAM under test: Combo guards DEV0 memory and DEV1 guards DEV1 memory.
  protected virtual task set_allowlist(bit allow);
    usb_combo_allowlist_t combo_users;
    usb_dev1_allowlist_t dev1_users;
    usb_axi_user_t denied_user;

    denied_user = authorized_user.value ^ usb_axi_user_t'(1);
    foreach (combo_users[index]) combo_users[index] = (allow || ram_target != USB_DEV0_SRAM) ? authorized_user.value : denied_user;
    foreach (dev1_users[index]) dev1_users[index] = (allow || ram_target != USB_DEV1_SRAM) ? authorized_user.value : denied_user;
    set_axi_user_allowlists(combo_users, dev1_users);
  endtask

  // Put back the filter policy the normal tests use.
  protected virtual task restore_policy();
    configure_ram_policies();
  endtask

  // Add to the checked-beat counts.
  protected virtual function void count_checked(int unsigned words);
    checked_beats += words;
    target_stats[ram_target].comparisons += words;
  endfunction

  // Log what a halfword (AxSIZE=1) write and read do to a RAM word. Only the DWORD
  // setup is checked.
  protected task run_halfword_probe();
    logic [31:0] offset = 32'h0000_5000;
    logic [31:0] seed_data = 32'ha1b2_c3d4;
    logic [15:0] halfword = 16'h5e6f;
    logic [31:0] actual;
    aaxi_master_tr request;

    `uvm_info("USB_DEV0_RAM_SIZE_PROBE", $sformatf("OBSERVATION ONLY: AxSIZE=1 write/read at AXI=0x%016h, seed DWORD=0x%08h, halfword=0x%04h; no unsupported-access response/data expectation", base_address + offset, seed_data, halfword), UVM_LOW)
    write32(ram_target, offset, seed_data, authorized_user);
    read32(ram_target, offset, actual, authorized_user);
    if (actual !== seed_data) `uvm_fatal("USB_DEV0_RAM_SIZE_PROBE", $sformatf("DWORD setup failed: expected=0x%08h actual=0x%08h", seed_data, actual))

    request = create_transaction(ram_target, offset, 1'b1, {16'b0, halfword}, authorized_user);
    request.size = 1;
    request.data.delete();
    request.strobes.delete();
    for (int unsigned byte_index = 0; byte_index < 2; byte_index++) begin
      request.data.push_back(halfword[byte_index * 8 +: 8]);
      request.strobes.push_back(1'b1);
    end
    execute_transaction(ram_target, 32'(request.addr), 1'b1, request);
    `uvm_info("USB_DEV0_RAM_SIZE_PROBE", $sformatf("Halfword write: AWSIZE=%0d bytes=%p strobes=%p BRESP=%0h", request.size, request.data, request.strobes, request.resp), UVM_LOW)

    request = create_transaction(ram_target, offset, 1'b0, '0, authorized_user);
    request.size = 1;
    execute_transaction(ram_target, 32'(request.addr), 1'b0, request);
    `uvm_info("USB_DEV0_RAM_SIZE_PROBE", $sformatf("Halfword read: ARSIZE=%0d bytes=%p RRESP=%p", request.size, request.data, request.rresp_Q), UVM_LOW)

    read32(ram_target, offset, actual, authorized_user);
    `uvm_info("USB_DEV0_RAM_SIZE_PROBE", $sformatf("Observed DWORD after halfword write/read: before=0x%08h after=0x%08h; observation is not a supported-access guarantee", seed_data, actual), UVM_LOW)
  endtask

  // Run every RAM test on one target (DEV0 or DEV1 RAM) and print a summary.
  protected task run_ram_cases(usb_target_e target);
    usb_axi_user_t axi_user;
    uvm_reg_map target_map;
    uvm_report_server reports;

    ram_target = target;
    bridge_target = target;
    bridge_name = usb_target_name(target);
    tag_prefix = "USB_DEV_RAM";
    expected_words.delete();
    launched = 0;
    finished = 0;
    positive_cases = 0;
    checked_beats = 0;
    max_reads = 0;
    max_writes = 0;
    read_write_overlap = 1'b0;
    hazard_cases = 0;
    policy_cases = 0;
    reset_abandoned = 0;
    reset_passed = 1'b0;
    target_map = map_for(ram_target);
    base_address = target_map.get_base_addr(UVM_NO_HIER);
    ram_bytes = sram_implemented_bytes(ram_target);
    if (!std::randomize(axi_user)) begin
      `uvm_fatal("USB_DEV0_RAM_RANDOM", $sformatf("%s USER randomization failed", usb_target_name(ram_target)))
    end
    authorized_user = usb_axi_user_override::with_value(axi_user);
    randomize_manager_ids();

    // Keep the selected USER; only the policy-change phase alters the allowlist and it restores it.
    configure_ram_policies();

    //Check 1-dword accesses and interleaved reads/writes
    run_single_beat_cases();

    //Test burst writes and reads with FIXED, INCR, and WRAP bursts of various lengths
    run_burst_cases();

    //Check that reads and writes can overlap on the bus without interfering with each other
    run_overlapping_accesses();

    run_fifo_saturation();

    //Race reads and writes to the same address and check AXI ordering rules
    run_same_address_hazards('h7000);

    // Flip the allowlist while a request is in flight; it must keep its acceptance-time decision.
    run_policy_change_cases('h7200);

    // Allowed-USER and denied-USER requests in flight together; each keeps its own filter decision.
    run_mixed_user_batch('h7a00);

    //Access first and last words of RAM
    run_boundary_cases();

    //Try AxSIZE=1 halfword accesses to see if they are supported and what happens to the other half of the word
    run_halfword_probe();

    // Last in the pass: pulse the AXI reset with a read and a write outstanding.
    run_reset_with_outstanding('h7600, 'h7700, 'h7800);

    if (launched != finished + reset_abandoned) `uvm_fatal("USB_DEV0_RAM_ACCOUNTING", "Requests remain outstanding")
    reports = uvm_report_server::get_server();
    `uvm_info("USB_DEV0_RAM_SUMMARY", $sformatf("%s %s positive_cases=%0d hazard_cases=%0d/6 policy_cases=%0d/4 mixed_user=%0s (%0d/%0d) reset=%0s checked_beats=%0d matrix_requests=%0d/%0d (items unreturned after reset=%0d) overlap=%0s max_reads=%0d max_writes=%0d; positive matrix accesses are in range with USER=0x%0h, ARSIZE/AWSIZE=2 only", reports.get_severity_count(UVM_ERROR) == 0 ? "PASS" : "FAIL", usb_target_name(ram_target), positive_cases, hazard_cases, policy_cases, mixed_passed ? "PASS" : "FAIL", mixed_requests, MIXED_SLOTS, reset_passed ? "PASS" : "FAIL", checked_beats, finished, launched, reset_abandoned, read_write_overlap ? "verified" : "N/A (single request)", max_reads, max_writes, authorized_user.value), UVM_LOW)
  endtask

  task body();
    completed = 1'b0;
    initialize_target_stats();
    run_ram_cases(USB_DEV0_SRAM);
    run_ram_cases(USB_DEV1_SRAM);
    completed = 1'b1;
  endtask
endclass
