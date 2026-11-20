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
// Count bus-accepted requests, not items waiting in the sequencer.
class usb_axi_inflight_callbacks extends aaxi_callbacks;
  `uvm_object_utils(usb_axi_inflight_callbacks)

  int unsigned reads;
  int unsigned writes;
  int unsigned accepted;
  typedef uvm_reg_addr_t address_queue_t[$];
  address_queue_t read_addresses[int unsigned];
  address_queue_t write_addresses[int unsigned];
  int unsigned read_ids[$];
  int unsigned write_ids[$];
  uvm_reg_addr_t read_history[$];
  uvm_reg_addr_t write_history[$];
  bit separated_read_id;
  bit separated_write_id;
  int unsigned reads_during_writes;
  int unsigned writes_during_reads;
  int unsigned writes_during_writes;

  function new(string name = "usb_axi_inflight_callbacks");
    super.new(name);
  endfunction

  // Called when the bus accepts a read address. Record its ID and address, and
  // note when an ID repeats after a different ID.
  virtual task master_read_addr_done(aaxi_device_class bfm, ref aaxi_master_tr tn);
    if (read_ids.size() > 0 && read_ids[$] != tn.id && read_addresses[tn.id].size() > 0) separated_read_id = 1'b1;
    read_addresses[tn.id].push_back(tn.addr);
    read_history.push_back(tn.addr);
    read_ids.push_back(tn.id);
    if (writes > 0) reads_during_writes++;
    reads++;
    accepted++;
  endtask

  // Called when the bus accepts a write address. Record its ID and address, and
  // note when an ID repeats after a different ID.
  virtual task master_write_addr_done(aaxi_device_class bfm, ref aaxi_master_tr tn);
    if (write_ids.size() > 0 && write_ids[$] != tn.id && write_addresses[tn.id].size() > 0) separated_write_id = 1'b1;
    write_addresses[tn.id].push_back(tn.addr);
    write_history.push_back(tn.addr);
    write_ids.push_back(tn.id);
    if (reads > 0) writes_during_reads++;
    if (writes > 0) writes_during_writes++;
    writes++;
    accepted++;
  endtask

  // AXI A6.5.1/A6.6.1: same-ID responses return in request order.
  virtual task read_done(aaxi_device_class bfm, ref aaxi_master_tr tn);
    if (reads == 0) `uvm_fatal("USB_AXI_INFLIGHT", "Read completed without an accepted address")
    if (read_addresses[tn.id].size() == 0 || tn.addr !== read_addresses[tn.id][0]) begin
      `uvm_fatal("USB_AXI_ORDER", $sformatf("Read completion out of accepted AR order: ID=%0d addr=0x%016h pending=%p", tn.id, tn.addr, read_addresses[tn.id]))
    end
    void'(read_addresses[tn.id].pop_front());
    reads--;
  endtask

  // Called when a write finishes. It must be the oldest pending write with that ID.
  virtual task write_done(aaxi_device_class bfm, ref aaxi_master_tr tn);
    if (writes == 0) `uvm_fatal("USB_AXI_INFLIGHT", "Write completed without an accepted address")
    if (write_addresses[tn.id].size() == 0 || tn.addr !== write_addresses[tn.id][0]) begin
      `uvm_fatal("USB_AXI_ORDER", $sformatf("Write completion out of accepted AW order: ID=%0d addr=0x%016h pending=%p", tn.id, tn.addr, write_addresses[tn.id]))
    end
    void'(write_addresses[tn.id].pop_front());
    writes--;
  endtask
endclass

// Shared helpers and spec-based scenarios for the USB AXI-to-AHB bridge sequences. Each
// sequence sets the bridge variables below and supplies policy controls through the hooks.
virtual class usb_axi_bridge_base_seq extends usb_base_seq;
  localparam int unsigned HAZARD_STALL = 512;
  localparam int unsigned HAZARD_DATA_DELAY = 64;
  localparam int unsigned POLICY_BEATS = 8;
  localparam int unsigned POLICY_STALL = 128;
  localparam int unsigned POLICY_DATA_DELAY = 64;
  localparam int unsigned RESET_BEATS = 16;
  localparam int unsigned RESET_STALL = 256;
  localparam int unsigned RESET_DATA_DELAY = 64;
  localparam int unsigned RESET_CYCLES = 16;
  localparam int unsigned RESET_SETTLE = 32;
  localparam int unsigned MIXED_SLOTS = 8;
  localparam int unsigned MIXED_SLOT_WORDS = 16;
  localparam int unsigned MIXED_STALL = 128;
  localparam int unsigned MIXED_DATA_DELAY = 32;
  localparam string BUS_RESET_PATH = "usb_top_tb.bus_reset_n";

  typedef struct {
    bit is_write;
    bit allowed;
    int unsigned beats;
  } mixed_user_case_t;

  bit completed;
  // Set by each sequence before it runs any shared scenario.
  protected usb_target_e bridge_target;  // AXI manager and map that carry the shared scenarios
  protected string bridge_name;          // name used in PASS and OBSERVATION messages
  protected string tag_prefix;           // report ID prefix, e.g. USB_COMBO gives USB_COMBO_HAZARD
  protected usb_axi_user_override authorized_user;
  protected uvm_reg_addr_t base_address;
  protected int unsigned launched;
  protected int unsigned finished;
  protected usb_axi_inflight_callbacks inflight_tracker;
  protected time inflight_timeout;
  protected int unsigned hazard_cases;
  protected int unsigned policy_cases;
  protected int unsigned reset_abandoned;
  protected bit reset_passed;
  protected int unsigned mixed_requests;
  protected bit mixed_passed;

  function new(string name = "usb_axi_bridge_base_seq");
    super.new(name);
  endfunction

  // Allow: every allowlist entry guarding the target is the test USER. Deny: none is.
  pure virtual protected task set_allowlist(bit allow);
  // Reprogram the policy the sequence's normal phases expect.
  pure virtual protected task restore_policy();
  // Add to the sequence's count of checked data words.
  pure virtual protected function void count_checked(int unsigned words);

  // Target-specific checks after reset, before the post-reset burst.
  virtual protected task post_reset_checks(output bit passed);
    passed = 1'b1;
  endtask

  // Return one beat of a request's data as a DWORD.
  protected function logic [31:0] data_word(aaxi_master_tr request, int unsigned beat);
    logic [31:0] data;

    for (int unsigned lane = 0; lane < 4; lane++) data[lane * 8 +: 8] = request.data[4 * beat + lane];
    return data;
  endfunction

  // AXI4 A3.4.1 for DWORD beats: FIXED repeats, INCR advances, WRAP stays in its aligned window.
  protected function uvm_reg_addr_t burst_beat_address(aaxi_burst_type burst, uvm_reg_addr_t start, int unsigned beats, int unsigned beat);
    uvm_reg_addr_t window_bytes = 4 * beats;

    case (burst)
      AAXI_BURST_FIXED: return start;
      AAXI_BURST_INCR:  return start + 4 * beat;
      AAXI_BURST_WRAP:  return (start / window_bytes) * window_bytes +
                               ((start % window_bytes + 4 * beat) % window_bytes);
      default: begin
        `uvm_fatal({tag_prefix, "_GEOMETRY"}, "Unexpected DWORD burst type")
        return '0;
      end
    endcase
  endfunction

  // Address of one beat of a request, following its burst type.
  protected function uvm_reg_addr_t beat_address(aaxi_master_tr request, int unsigned beat);
    return burst_beat_address(aaxi_burst_type'(request.burst), request.addr, int'(request.len) + 1, beat);
  endfunction

  // Lowest address and DWORD count touched by a burst.
  protected function void burst_span(aaxi_burst_type burst, uvm_reg_addr_t start, int unsigned beats, output uvm_reg_addr_t first, output int unsigned words);
    first = burst == AAXI_BURST_WRAP ? (start / (4 * beats)) * (4 * beats) : start;
    words = burst == AAXI_BURST_FIXED ? 1 : beats;
  endfunction

  // Full strobes on every beat: USB does not honor WSTRB masking.
  protected function void set_write_words(aaxi_master_tr request, logic [31:0] words[]);
    request.data.delete();
    request.strobes.delete();
    foreach (words[beat]) begin
      for (int unsigned lane = 0; lane < 4; lane++) begin
        request.data.push_back(words[beat][lane * 8 +: 8]);
        request.strobes.push_back(1'b1);
      end
    end
  endfunction

  // Three distinct random full-width IDs in the order A,B,A,C,B,A, so each
  // same-ID repeat is separated by other IDs.
  protected function void separated_id_pattern(output aaxi_id_t ids[6]);
    aaxi_id_t a, b, c;

    if (!std::randomize(a, b, c) with { unique {a, b, c}; }) begin
      `uvm_fatal({tag_prefix, "_ID"}, "Distinct AXI ID randomization failed")
    end
    ids = '{a, b, a, c, b, a};
  endfunction

  // Authorized INCR DWORD request on the target's manager.
  // USER defaults to the authorized test USER.
  protected function aaxi_master_tr incr_request(string label, logic [31:0] offset, bit is_write, int unsigned beats, usb_axi_user_override user = null);
    aaxi_master_tr request;
    usb_axi_user_override request_user;

    request_user = (user == null) ? authorized_user : user;
    request = create_transaction(bridge_target, offset, is_write, '0, request_user);
    request.set_name(label);
    request.len = beats - 1;
    request.wuser_A = new[beats];
    foreach (request.wuser_A[beat]) request.wuser_A[beat] = request_user.value;
    return request;
  endfunction

  // Build an authorized INCR read of the given number of DWORDs.
  protected function aaxi_master_tr build_read(string label, logic [31:0] offset, int unsigned beats, usb_axi_user_override user = null);
    return incr_request(label, offset, 1'b0, beats, user);
  endfunction

  // Build an authorized INCR write that carries the given words.
  protected function aaxi_master_tr build_write(string label, logic [31:0] offset, logic [31:0] words[], usb_axi_user_override user = null);
    aaxi_master_tr request;

    request = incr_request(label, offset, 1'b1, words.size(), user);
    set_write_words(request, words);
    return request;
  endfunction

  // Response stalls delay BREADY, or RREADY before every read beat unless stall_each_read_beat is clear.
  protected task issue_request(aaxi_master_tr request, int unsigned response_stall = 0, time request_timeout = 0, int unsigned write_data_delay = 0, bit stall_each_read_beat = 1'b1);
    usb_axi_single_request_seq child;

    if (bridge_name == "" || tag_prefix == "") `uvm_fatal("USB_AXI_BRIDGE", "Set bridge_target, bridge_name, and tag_prefix before running shared scenarios")
    if (request.kind == AAXI_WRITE) begin
      request.b_valid_ready_delay = response_stall;
      if (write_data_delay > 0) request.adw_valid_delay = int'(write_data_delay);
    end else begin
      request.ar_handshake_rready_delay = response_stall;
      if (stall_each_read_beat) begin
        foreach (request.resp_ready_delay[beat]) request.resp_ready_delay[beat] = 16'(response_stall);
      end
    end
    child = usb_axi_single_request_seq::type_id::create($sformatf("%s_request%0d", request.get_name(), launched));
    child.target = bridge_target;
    child.transaction = request;
    child.timeout = request_timeout;
    launched++;
    child.start(p_sequencer, this);
    finished++;
  endtask

  // OKAY on the single B response or on every R beat.
  protected function bit check_okay(aaxi_master_tr request);
    bit is_write = request.kind == AAXI_WRITE;
    int unsigned count = is_write ? 1 : int'(request.len) + 1;

    if (!is_write && request.rresp_Q.size() != count) begin
      `uvm_fatal({tag_prefix, "_RESPONSE"}, $sformatf("%s AXI=0x%016h: received %0d/%0d read responses", request.get_name(), request.addr, request.rresp_Q.size(), count))
    end
    for (int unsigned beat = 0; beat < count; beat++) begin
      if ((is_write ? request.resp : request.rresp_Q[beat]) !== AAXI_RESP_OKAY) begin
        `uvm_error({tag_prefix, "_RESPONSE"}, $sformatf("%s %s AXI=0x%016h USER=0x%0h beat=%0d/%0d expected_resp=%0h actual_resp=%0h", request.get_name(), is_write ? "write" : "read", request.addr, is_write ? request.awuser : request.aruser, beat, count, AAXI_RESP_OKAY, is_write ? request.resp : request.rresp_Q[beat]))
        return 1'b0;
      end
    end
    return 1'b1;
  endfunction

  // Check that a read returned OKAY and the expected word on every beat.
  protected function bit check_read_words(aaxi_master_tr request, logic [31:0] expected[]);
    if (!check_okay(request)) return 1'b0;
    if (request.data.size() != 4 * expected.size()) begin
      `uvm_fatal({tag_prefix, "_DATA"}, $sformatf("%s AXI=0x%016h returned %0d bytes for %0d beats", request.get_name(), request.addr, request.data.size(), expected.size()))
    end
    foreach (expected[beat]) begin
      if (data_word(request, beat) !== expected[beat]) begin
        `uvm_fatal({tag_prefix, "_DATA"}, $sformatf("%s AXI=0x%016h beat=%0d/%0d expected=0x%08h actual=0x%08h", request.get_name(), beat_address(request, beat), beat, expected.size(), expected[beat], data_word(request, beat)))
      end
    end
    count_checked(expected.size());
    return 1'b1;
  endfunction

  // Write random words to an INCR span and confirm them with a readback.
  protected task seed_words(string label, logic [31:0] offset, int unsigned beats, output logic [31:0] words[], output bit seeded);
    aaxi_master_tr request;

    words = new[beats];
    foreach (words[beat]) words[beat] = $urandom();
    request = build_write({label, "-seed"}, offset, words);
    issue_request(request);
    seeded = check_okay(request);
    if (!seeded) return;
    request = build_read({label, "-seed-readback"}, offset, beats);
    issue_request(request);
    seeded = check_read_words(request, words);
  endtask

  // Count bus-accepted requests on the target manager; budget timeouts for deliberate stalls.
  protected task start_inflight_tracker(string name, int unsigned stall_cycles);
    aaxi_sequencer manager;
    realtime clock_sample;

    manager = sequencer_for(bridge_target);
    inflight_tracker = usb_axi_inflight_callbacks::type_id::create(name);
    p_sequencer.cfg.wait_bus_negedge();
    clock_sample = $realtime;
    p_sequencer.cfg.wait_bus_negedge();
    inflight_timeout = transfer_timeout() + time'(stall_cycles * ($realtime - clock_sample));
    manager.cfg.agent.add_callback(inflight_tracker);
  endtask

  // Remove the tracker. By default, stop the test if any request is still pending.
  protected task stop_inflight_tracker(string tag, bit require_idle = 1'b1);
    aaxi_sequencer manager;

    manager = sequencer_for(bridge_target);
    manager.cfg.agent.delete_callback(inflight_tracker);
    if (require_idle && (inflight_tracker.reads != 0 || inflight_tracker.writes != 0)) begin
      `uvm_fatal(tag, $sformatf("Requests remain outstanding: reads=%0d writes=%0d", inflight_tracker.reads, inflight_tracker.writes))
    end
  endtask

  // Wait until the bus has accepted count requests; stop the test if it takes too long.
  protected task wait_for_acceptance(int unsigned count, string label);
    for (int unsigned cycle = 0; inflight_tracker.accepted < count; cycle++) begin
      if (cycle >= 4096) `uvm_fatal({tag_prefix, "_INFLIGHT"}, $sformatf("%s: request not accepted within %0d cycles", label, cycle))
      p_sequencer.cfg.wait_bus_negedge();
    end
  endtask

  // AXI A6.1/A6.2: a read racing an uncompleted write may return each byte's old or new value.
  // A6.5.1: once a same-ID read observes the write, later same-ID reads must observe it too.
  protected function bit check_racing_read(aaxi_master_tr request, logic [31:0] old_words[], logic [31:0] new_words[], inout bit [3:0] seen_new[], output int unsigned new_bytes);
    logic [7:0] actual, old_byte, new_byte;

    new_bytes = 0;
    if (!check_okay(request)) return 1'b0;
    if (request.data.size() != 4 * old_words.size()) begin
      `uvm_fatal({tag_prefix, "_HAZARD"}, $sformatf("%s AXI=0x%016h returned %0d bytes for %0d beats", request.get_name(), request.addr, request.data.size(), old_words.size()))
    end
    foreach (old_words[beat]) begin
      for (int unsigned lane = 0; lane < 4; lane++) begin
        actual = request.data[4 * beat + lane];
        old_byte = old_words[beat][8 * lane +: 8];
        new_byte = new_words[beat][8 * lane +: 8];
        if (actual === new_byte) begin
          seen_new[beat][lane] = 1'b1;
          new_bytes++;
        end else if (actual !== old_byte) begin
          `uvm_fatal({tag_prefix, "_HAZARD"}, $sformatf("%s beat=%0d lane=%0d AXI=0x%016h: byte=0x%02h is neither old=0x%02h nor new=0x%02h", request.get_name(), beat, lane, beat_address(request, beat), actual, old_byte, new_byte))
        end else if (seen_new[beat][lane]) begin
          `uvm_fatal({tag_prefix, "_HAZARD"}, $sformatf("%s beat=%0d lane=%0d AXI=0x%016h: returned old byte=0x%02h after an earlier same-ID read observed new=0x%02h (AXI A6.5.1)", request.get_name(), beat, lane, beat_address(request, beat), actual, new_byte))
        end
      end
    end
    count_checked(old_words.size());
    return 1'b1;
  endfunction

  // Race same-address reads and a write; the second side starts once the first is accepted
  // and stalled. After both complete, A6.5.2 requires a later read to return the new data.
  protected task race_read_write(string label, int unsigned beats, logic [31:0] offset, bit write_first, int unsigned read_count, int unsigned data_delay = 0);
    aaxi_master_tr write_request, final_read;
    aaxi_master_tr read_requests[];
    logic [31:0] old_words[], new_words[];
    bit [3:0] seen_new[];
    int unsigned first, overlapped, new_bytes;
    string observed;
    bit passed;

    seed_words(label, offset, beats, old_words, passed);
    if (!passed) return;
    new_words = new[beats];
    // Every byte differs, so each returned byte is unambiguously old or new.
    foreach (new_words[beat]) new_words[beat] = ~old_words[beat];
    write_request = build_write({label, "-write"}, offset, new_words);
    read_requests = new[read_count];
    foreach (read_requests[index]) read_requests[index] = build_read($sformatf("%s-read%0d", label, index), offset, beats);
    first = inflight_tracker.accepted;
    overlapped = write_first ? inflight_tracker.reads_during_writes : inflight_tracker.writes_during_reads;

    fork
      begin
        if (write_first) issue_request(write_request, HAZARD_STALL, inflight_timeout, data_delay);
        else issue_request(read_requests[0], HAZARD_STALL, inflight_timeout);
      end
      begin
        wait_for_acceptance(first + 1, label);
        if (write_first) begin
          foreach (read_requests[index]) issue_request(read_requests[index], 0, inflight_timeout);
        end else issue_request(write_request, 0, inflight_timeout);
      end
    join

    if (write_first && inflight_tracker.reads_during_writes - overlapped != read_count) begin
      `uvm_fatal({tag_prefix, "_HAZARD"}, $sformatf("%s: only %0d/%0d reads were accepted while the write was outstanding", label, inflight_tracker.reads_during_writes - overlapped, read_count))
    end
    if (!write_first && inflight_tracker.writes_during_reads == overlapped) begin
      `uvm_fatal({tag_prefix, "_HAZARD"}, $sformatf("%s: write was not accepted while the read was outstanding", label))
    end

    passed = 1'b1;
    seen_new = new[beats];
    foreach (read_requests[index]) begin
      if (!check_racing_read(read_requests[index], old_words, new_words, seen_new, new_bytes)) passed = 1'b0;
      observed = {observed, $sformatf("%s%0d/%0d", index == 0 ? "" : ",", new_bytes, 4 * beats)};
    end
    passed &= check_okay(write_request);
    if (!passed) return;
    final_read = build_read({label, "-after-completion"}, offset, beats);
    issue_request(final_read);
    if (!check_read_words(final_read, new_words)) return;
    hazard_cases++;
    `uvm_info({tag_prefix, "_HAZARD"}, $sformatf("PASS %s %s offset=0x%08h beats=%0d %s-first, new bytes per racing read=[%s]; read after both completions returned new data", bridge_name, label, offset, beats, write_first ? "write" : "read", observed), UVM_LOW)
  endtask

  // AXI A6.6.1: a later same-ID write to the same location must be ordered after the earlier one.
  protected task race_same_id_writes(string label, logic [31:0] offset);
    aaxi_master_tr first_request, second_request, final_read;
    logic [31:0] old_words[], first_words[], second_words[];
    int unsigned first, overlapped;
    bit passed;

    seed_words(label, offset, 1, old_words, passed);
    if (!passed) return;
    first_words = '{~old_words[0]};
    second_words = '{old_words[0] ^ 32'h5555_5555};
    first_request = build_write({label, "-first"}, offset, first_words);
    second_request = build_write({label, "-second"}, offset, second_words);
    first = inflight_tracker.accepted;
    overlapped = inflight_tracker.writes_during_writes;
    fork
      issue_request(first_request, HAZARD_STALL, inflight_timeout);
      begin
        wait_for_acceptance(first + 1, label);
        issue_request(second_request, 0, inflight_timeout);
      end
    join
    if (inflight_tracker.writes_during_writes == overlapped) begin
      `uvm_fatal({tag_prefix, "_HAZARD"}, $sformatf("%s: second write was not accepted while the first was outstanding", label))
    end
    passed = check_okay(first_request);
    passed &= check_okay(second_request);
    if (!passed) return;
    final_read = build_read({label, "-after-completion"}, offset, 1);
    issue_request(final_read);
    if (!check_read_words(final_read, second_words)) return;
    hazard_cases++;
    `uvm_info({tag_prefix, "_HAZARD"}, $sformatf("PASS %s %s offset=0x%08h ID=%0d first=0x%08h second=0x%08h; final value is the second write", bridge_name, label, offset, first_request.id, first_words[0], second_words[0]), UVM_LOW)
  endtask

  // Six cases in consecutive 64-byte slots starting at first_offset.
  protected task run_same_address_hazards(logic [31:0] first_offset);
    start_inflight_tracker("hazard_tracker", 4 * HAZARD_STALL + HAZARD_DATA_DELAY + 256);
    race_read_write("RAW", 1, first_offset, 1'b1, 1);
    // Delaying W behind AW gives the in-order reads a chance to see old, then new data.
    race_read_write("RAW-monotonic-reads", 1, first_offset + 'h40, 1'b1, 4, HAZARD_DATA_DELAY);
    race_read_write("RAW-INCR4", 4, first_offset + 'h80, 1'b1, 1);
    race_read_write("WAR", 1, first_offset + 'hc0, 1'b0, 1);
    race_read_write("WAR-INCR4", 4, first_offset + 'h100, 1'b0, 1);
    race_same_id_writes("WAW-same-ID", first_offset + 'h140);
    stop_inflight_tracker({tag_prefix, "_HAZARD"});
  endtask

  // HW spec: a denied read returns SLVERR and zero data on every requested beat.
  protected function bit check_denied_read(aaxi_master_tr request);
    int unsigned beats = int'(request.len) + 1;

    if (request.rresp_Q.size() != beats || request.data.size() != 4 * beats) begin
      `uvm_fatal({tag_prefix, "_POLICY"}, $sformatf("%s denied read AXI=0x%016h returned %0d responses/%0d bytes for %0d beats", request.get_name(), request.addr, request.rresp_Q.size(), request.data.size(), beats))
    end
    foreach (request.rresp_Q[beat]) begin
      if (request.rresp_Q[beat] !== AAXI_RESP_SLVERR) begin
        `uvm_error({tag_prefix, "_POLICY"}, $sformatf("%s denied read beat=%0d/%0d AXI=0x%016h USER=0x%0h expected_resp=%0h actual_resp=%0h", request.get_name(), beat, beats, request.addr, request.aruser, AAXI_RESP_SLVERR, request.rresp_Q[beat]))
        return 1'b0;
      end
    end
    foreach (request.data[index]) begin
      if (request.data[index] !== 8'h00) begin
        `uvm_fatal({tag_prefix, "_POLICY"}, $sformatf("%s denied read beat=%0d byte=%0d AXI=0x%016h: expected zero data, actual=0x%02h", request.get_name(), index / 4, index % 4, request.addr, request.data[index]))
      end
    end
    count_checked(beats);
    return 1'b1;
  endfunction

  // HW spec: a denied write returns one SLVERR and does not access the target.
  protected function bit check_denied_write(aaxi_master_tr request);
    if (request.resp !== AAXI_RESP_SLVERR) begin
      `uvm_error({tag_prefix, "_POLICY"}, $sformatf("%s denied write AXI=0x%016h USER=0x%0h beats=%0d expected_resp=%0h actual_resp=%0h", request.get_name(), request.addr, request.awuser, int'(request.len) + 1, AAXI_RESP_SLVERR, request.resp))
      return 1'b0;
    end
    return 1'b1;
  endfunction

  // HW spec: the filter decision is captured at address acceptance and kept for the whole
  // request, so flipping the allowlist mid-request affects only later requests.
  protected task policy_change_case(string label, logic [31:0] offset, bit is_write, bit start_allowed);
    aaxi_master_tr request, probe;
    logic [31:0] old_words[], new_words[], probe_words[], expected[];
    int unsigned first;
    bit still_outstanding, passed;

    seed_words(label, offset, POLICY_BEATS, old_words, passed);
    if (!passed) return;
    expected = old_words;
    if (!start_allowed) set_allowlist(1'b0);
    if (is_write) begin
      new_words = new[POLICY_BEATS];
      foreach (new_words[beat]) new_words[beat] = ~old_words[beat];
      request = build_write({label, "-inflight"}, offset, new_words);
    end else request = build_read({label, "-inflight"}, offset, POLICY_BEATS);
    first = inflight_tracker.accepted;
    fork
      // Stall R/B and delay W so the request is still in flight when the policy flips.
      issue_request(request, POLICY_STALL, inflight_timeout, is_write ? POLICY_DATA_DELAY : 0);
      begin
        wait_for_acceptance(first + 1, label);
        set_allowlist(!start_allowed);
        still_outstanding = is_write ? inflight_tracker.writes > 0 : inflight_tracker.reads > 0;
      end
    join
    if (!still_outstanding) begin
      `uvm_fatal({tag_prefix, "_POLICY"}, $sformatf("%s: request completed before the policy change finished", label))
    end
    if (!start_allowed) passed = is_write ? check_denied_write(request) : check_denied_read(request);
    else if (!is_write) passed = check_read_words(request, old_words);
    else begin
      passed = check_okay(request);
      expected = new_words;
    end

    // A request accepted after the change must follow the new policy.
    if (is_write && start_allowed) begin
      probe_words = new[POLICY_BEATS];
      foreach (probe_words[beat]) probe_words[beat] = old_words[beat] ^ 32'h5a5a_5a5a;
      probe = build_write({label, "-after-change"}, offset, probe_words);
      issue_request(probe);
      passed &= check_denied_write(probe);
    end else begin
      probe = build_read({label, "-after-change"}, offset, POLICY_BEATS);
      issue_request(probe);
      passed &= start_allowed ? check_denied_read(probe) : check_read_words(probe, expected);
    end

    // Authorized readback shows which writes reached the target.
    if (start_allowed) set_allowlist(1'b1);
    probe = build_read({label, "-final-readback"}, offset, POLICY_BEATS);
    issue_request(probe);
    passed &= check_read_words(probe, expected);
    if (!passed) return;
    policy_cases++;
    `uvm_info({tag_prefix, "_POLICY"}, $sformatf("PASS %s %s offset=0x%08h beats=%0d: %s %s accepted while %s kept that decision after the change; the next request followed the new policy", bridge_name, label, offset, POLICY_BEATS, is_write ? "write" : "read", start_allowed ? "OKAY" : "SLVERR", start_allowed ? "allowed" : "denied"), UVM_LOW)
  endtask

  // Four cases in consecutive 64-byte slots starting at first_offset.
  protected task run_policy_change_cases(logic [31:0] first_offset);
    start_inflight_tracker("policy_tracker", (POLICY_BEATS + 2) * POLICY_STALL + POLICY_DATA_DELAY);
    policy_change_case("allow-to-deny-read", first_offset, 1'b0, 1'b1);
    policy_change_case("allow-to-deny-write", first_offset + 'h40, 1'b1, 1'b1);
    policy_change_case("deny-to-allow-read", first_offset + 'h80, 1'b0, 1'b0);
    policy_change_case("deny-to-allow-write", first_offset + 'hc0, 1'b1, 1'b0);
    stop_inflight_tracker({tag_prefix, "_POLICY"});
    restore_policy();
  endtask

  // Batch slot owning a pending request address, or -1 for traffic outside the batch.
  protected function int mixed_slot(uvm_reg_addr_t address, logic [31:0] first_offset);
    uvm_reg_addr_t start = base_address + uvm_reg_addr_t'(first_offset);

    if (address < start || address >= start + MIXED_SLOTS * 4 * MIXED_SLOT_WORDS) return -1;
    return int'((address - start) / (4 * MIXED_SLOT_WORDS));
  endfunction

  // Count how many pending batch requests are allowed and how many are denied.
  protected function void count_mixed_pending(usb_axi_inflight_callbacks::address_queue_t pending[int unsigned], logic [31:0] first_offset, mixed_user_case_t cases[MIXED_SLOTS], output int unsigned allowed, output int unsigned denied);
    int slot;

    allowed = 0;
    denied = 0;
    foreach (pending[id]) begin
      for (int unsigned index = 0; index < pending[id].size(); index++) begin
        slot = mixed_slot(pending[id][index], first_offset);
        if (slot < 0) continue;
        if (cases[slot].allowed) allowed++;
        else denied++;
      end
    end
  endfunction

  // if/else avoids VCS padding the shorter literal of a ?: pair.
  protected function string mixed_name(mixed_user_case_t mixed_case);
    string user_kind, direction;

    if (mixed_case.allowed) user_kind = "allowed";
    else user_kind = "denied";
    if (mixed_case.is_write) direction = "write";
    else direction = "read";
    return {user_kind, "-", direction};
  endfunction

  // Accepted order of the batch, e.g. "allowed-write-16 denied-write-7".
  protected function string mixed_order(uvm_reg_addr_t history[$], logic [31:0] first_offset, mixed_user_case_t cases[MIXED_SLOTS]);
    string order;
    int slot;

    foreach (history[index]) begin
      slot = mixed_slot(history[index], first_offset);
      if (slot < 0) continue;
      if (order.len() > 0) order = {order, " "};
      order = {order, $sformatf("%s-%0d", mixed_name(cases[slot]), cases[slot].beats)};
    end
    return order;
  endfunction

  // HW spec: the filter decides each request at address acceptance, so allowed-USER and
  // denied-USER requests in flight together must each get their own result: OKAY, or SLVERR
  // with zero read data and no write. AXI A6.5.1 same-ID order must hold across the mix.
  // One 64-byte slot per request; reads and writes each alternate allowed/denied.
  protected task run_mixed_user_batch(logic [31:0] first_offset);
    mixed_user_case_t cases[MIXED_SLOTS];
    aaxi_master_tr requests[MIXED_SLOTS];
    aaxi_master_tr readback;
    logic [31:0] slot_words[MIXED_SLOTS][];
    logic [31:0] write_words[MIXED_SLOTS][];
    logic [31:0] expected[];
    usb_axi_user_override denied_user;
    logic [31:0] offset;
    string label;
    bit seeded, launches_done, passed;
    bit mixed_reads_seen, mixed_writes_seen;
    int unsigned allowed_reads, denied_reads, allowed_writes, denied_writes, max_pending;

    // Lengths include non-power-of-2 bursts; every request fits its 16-word slot.
    cases = '{'{1'b1, 1'b1, 16}, '{1'b1, 1'b0, 7}, '{1'b0, 1'b1, 8}, '{1'b0, 1'b0, 3},
              '{1'b1, 1'b0, 12}, '{1'b1, 1'b1, 5}, '{1'b0, 1'b0, 16}, '{1'b0, 1'b1, 9}};
    denied_user = usb_axi_user_override::with_value(authorized_user.value ^ usb_axi_user_t'(1));
    mixed_requests = 0;
    mixed_passed = 1'b0;
    passed = 1'b1;
    launches_done = 1'b0;
    mixed_reads_seen = 1'b0;
    mixed_writes_seen = 1'b0;
    max_pending = 0;

    foreach (cases[slot]) begin
      seed_words($sformatf("mixed-slot%0d", slot), first_offset + 4 * MIXED_SLOT_WORDS * slot, MIXED_SLOT_WORDS, slot_words[slot], seeded);
      if (!seeded) return;
    end
    foreach (cases[slot]) begin
      offset = first_offset + 4 * MIXED_SLOT_WORDS * slot;
      label = $sformatf("mixed%0d-%s", slot, mixed_name(cases[slot]));
      if (cases[slot].is_write) begin
        write_words[slot] = new[cases[slot].beats];
        for (int unsigned beat = 0; beat < cases[slot].beats; beat++) write_words[slot][beat] = ~slot_words[slot][beat];
        requests[slot] = build_write(label, offset, write_words[slot], cases[slot].allowed ? authorized_user : denied_user);
      end else requests[slot] = build_read(label, offset, cases[slot].beats, cases[slot].allowed ? authorized_user : denied_user);
    end

    start_inflight_tracker("mixed_user_tracker", (4 * MIXED_SLOT_WORDS + MIXED_SLOTS) * MIXED_STALL + MIXED_DATA_DELAY);
    fork
      begin
        // Stall R/B so earlier requests are still outstanding when later ones are accepted.
        foreach (requests[slot]) begin
          automatic int unsigned index = slot;
          fork
            issue_request(requests[index], MIXED_STALL, inflight_timeout, requests[index].kind == AAXI_WRITE ? MIXED_DATA_DELAY : 0);
          join_none
          p_sequencer.cfg.wait_bus_negedge();
        end
        wait fork;
        launches_done = 1'b1;
      end
      while (!launches_done) begin
        p_sequencer.cfg.wait_bus_negedge();
        count_mixed_pending(inflight_tracker.read_addresses, first_offset, cases, allowed_reads, denied_reads);
        count_mixed_pending(inflight_tracker.write_addresses, first_offset, cases, allowed_writes, denied_writes);
        if (allowed_reads > 0 && denied_reads > 0) mixed_reads_seen = 1'b1;
        if (allowed_writes > 0 && denied_writes > 0) mixed_writes_seen = 1'b1;
        if (allowed_reads + denied_reads + allowed_writes + denied_writes > max_pending) begin
          max_pending = allowed_reads + denied_reads + allowed_writes + denied_writes;
        end
      end
    join
    stop_inflight_tracker({tag_prefix, "_MIXED_USER"});
    if (!mixed_reads_seen || !mixed_writes_seen) begin
      `uvm_fatal({tag_prefix, "_MIXED_USER"}, $sformatf("%s: allowed and denied requests were not outstanding together (reads=%0d writes=%0d)", bridge_name, mixed_reads_seen, mixed_writes_seen))
    end

    foreach (cases[slot]) begin
      if (cases[slot].is_write && cases[slot].allowed) begin
        if (check_okay(requests[slot])) begin
          for (int unsigned beat = 0; beat < cases[slot].beats; beat++) slot_words[slot][beat] = write_words[slot][beat];
          mixed_requests++;
        end else passed = 1'b0;
      end else if (cases[slot].is_write) begin
        if (check_denied_write(requests[slot])) mixed_requests++;
        else passed = 1'b0;
      end else if (cases[slot].allowed) begin
        expected = new[cases[slot].beats](slot_words[slot]);
        if (check_read_words(requests[slot], expected)) mixed_requests++;
        else passed = 1'b0;
      end else begin
        if (check_denied_read(requests[slot])) mixed_requests++;
        else passed = 1'b0;
      end
    end

    // Authorized readback of whole slots: allowed writes landed only on their beats; denied writes changed nothing.
    foreach (cases[slot]) begin
      readback = build_read($sformatf("mixed%0d-final-readback", slot), first_offset + 4 * MIXED_SLOT_WORDS * slot, MIXED_SLOT_WORDS);
      issue_request(readback);
      passed &= check_read_words(readback, slot_words[slot]);
    end
    if (!passed) return;
    mixed_passed = 1'b1;
    `uvm_info({tag_prefix, "_MIXED_USER"}, $sformatf("PASS %s offset=0x%08h: %0d/%0d requests (USER=0x%0h allowed, USER=0x%0h denied) each got its own result while in flight together; max_outstanding=%0d; accepted reads: %s; accepted writes: %s", bridge_name, first_offset, mixed_requests, MIXED_SLOTS, authorized_user.value, denied_user.value, max_pending, mixed_order(inflight_tracker.read_history, first_offset, cases), mixed_order(inflight_tracker.write_history, first_offset, cases)), UVM_LOW)
  endtask

  // AXI A3.1.2: while ARESETn is low the manager drives ARVALID/AWVALID/WVALID LOW and the
  // subordinate drives RVALID/BVALID LOW. Sample both sides at every falling edge of the pulse.
  protected task pulse_bus_reset(output int unsigned violations);
    aaxi_sequencer manager;
    string first_violation;

    manager = sequencer_for(bridge_target);
    violations = 0;
    p_sequencer.cfg.wait_bus_negedge();
    if (!uvm_hdl_deposit(BUS_RESET_PATH, 0)) `uvm_fatal({tag_prefix, "_RESET"}, $sformatf("Unable to assert %s", BUS_RESET_PATH))
    `uvm_info({tag_prefix, "_RESET"}, $sformatf("Asserted %s for %0d cycles with %s requests outstanding", BUS_RESET_PATH, RESET_CYCLES, bridge_name), UVM_LOW)
    repeat (RESET_CYCLES) begin
      p_sequencer.cfg.wait_bus_negedge();
      if (!p_sequencer.cfg.bus_in_reset()) `uvm_fatal({tag_prefix, "_RESET"}, "Bus reset did not stay asserted")
      if (manager.cfg.vif.ARVALID !== 1'b0 || manager.cfg.vif.AWVALID !== 1'b0 ||
          manager.cfg.vif.WVALID !== 1'b0 || manager.cfg.vif.RVALID !== 1'b0 ||
          manager.cfg.vif.BVALID !== 1'b0) begin
        if (violations == 0) begin
          first_violation = $sformatf("ARVALID=%b AWVALID=%b WVALID=%b RVALID=%b BVALID=%b at %0t", manager.cfg.vif.ARVALID, manager.cfg.vif.AWVALID, manager.cfg.vif.WVALID, manager.cfg.vif.RVALID, manager.cfg.vif.BVALID, $time);
        end
        violations++;
      end
    end
    if (violations > 0) begin
      `uvm_error({tag_prefix, "_RESET"}, $sformatf("%s: VALID not LOW during reset on %0d/%0d sampled cycles; first: %s", bridge_name, violations, RESET_CYCLES, first_violation))
    end
    // Release on a falling edge, as the testbench top does, so the next rising edge samples it high.
    if (!uvm_hdl_deposit(BUS_RESET_PATH, 1)) `uvm_fatal({tag_prefix, "_RESET"}, $sformatf("Unable to release %s", BUS_RESET_PATH))
    p_sequencer.cfg.wait_bus_posedge();
    if (p_sequencer.cfg.bus_in_reset()) `uvm_fatal({tag_prefix, "_RESET"}, "Bus reset did not release")
  endtask

  // Report only: no spec defines target contents after reset.
  protected task observe_after_reset(string label, logic [31:0] offset, logic [31:0] old_words[], logic [31:0] new_words[], output string summary);
    aaxi_master_tr request;
    int unsigned old_count, new_count, other_count;

    request = build_read({label, "-after-reset"}, offset, old_words.size());
    issue_request(request);
    if (!check_okay(request)) begin
      summary = "read failed";
      return;
    end
    if (request.data.size() != 4 * old_words.size()) begin
      `uvm_fatal({tag_prefix, "_RESET"}, $sformatf("%s AXI=0x%016h returned %0d bytes for %0d beats", request.get_name(), request.addr, request.data.size(), old_words.size()))
    end
    foreach (old_words[beat]) begin
      if (data_word(request, beat) === old_words[beat]) old_count++;
      else if (data_word(request, beat) === new_words[beat]) new_count++;
      else other_count++;
    end
    summary = $sformatf("old=%0d new=%0d other=%0d of %0d words", old_count, new_count, other_count, old_words.size());
  endtask

  // The AXI spec defines bus behavior during reset but not the fate of requests outstanding
  // when it asserts; those outcomes are logged as observations. Requests after reset must work.
  protected task run_reset_with_outstanding(logic [31:0] read_offset, logic [31:0] write_offset, logic [31:0] fresh_offset);
    aaxi_master_tr read_request, write_request, request;
    logic [31:0] old_read[], old_write[], new_write[], fresh_words[];
    bit read_done, write_done, passed, target_ok;
    int unsigned first, violations;
    string read_region, write_region;

    seed_words("reset-read", read_offset, RESET_BEATS, old_read, passed);
    if (!passed) return;
    seed_words("reset-write", write_offset, RESET_BEATS, old_write, passed);
    if (!passed) return;
    new_write = new[RESET_BEATS];
    foreach (new_write[beat]) new_write[beat] = ~old_write[beat];
    read_request = build_read("reset-read", read_offset, RESET_BEATS);
    write_request = build_write("reset-write", write_offset, new_write);

    start_inflight_tracker("reset_tracker", (RESET_BEATS + 2) * RESET_STALL + RESET_DATA_DELAY);
    first = inflight_tracker.accepted;
    fork
      begin
        fork
          begin
            issue_request(read_request, RESET_STALL, inflight_timeout);
            read_done = 1'b1;
          end
          begin
            wait_for_acceptance(first + 1, "reset-read");
            issue_request(write_request, RESET_STALL, inflight_timeout, RESET_DATA_DELAY);
            write_done = 1'b1;
          end
        join_none
        wait_for_acceptance(first + 2, "reset-write");
        if (inflight_tracker.reads == 0 || inflight_tracker.writes == 0) begin
          `uvm_fatal({tag_prefix, "_RESET"}, $sformatf("Need a read and a write outstanding at reset: reads=%0d writes=%0d", inflight_tracker.reads, inflight_tracker.writes))
        end
        pulse_bus_reset(violations);
        // Give the VIP time to report completions before abandoning the requests it purged.
        repeat (RESET_SETTLE) p_sequencer.cfg.wait_bus_negedge();
        disable fork;
      end
    join
    reset_abandoned += (read_done ? 0 : 1) + (write_done ? 0 : 1);
    stop_inflight_tracker({tag_prefix, "_RESET"}, 1'b0);
    // A purged Avery item can return without a bus response, so judge completion from the bus callbacks.
    `uvm_info({tag_prefix, "_RESET"}, $sformatf("OBSERVATION %s: in-flight read %s on the bus (sequence item %s); in-flight write %s on the bus (sequence item %s)", bridge_name, inflight_tracker.reads == 0 ? $sformatf("completed RRESP=%p", read_request.rresp_Q) : "got no final R beat", read_done ? "returned" : "never returned", inflight_tracker.writes == 0 ? $sformatf("completed BRESP=%0h", write_request.resp) : "got no B response", write_done ? "returned after the VIP reset purge" : "never returned"), UVM_LOW)

    restore_policy();
    observe_after_reset("reset-read", read_offset, old_read, old_read, read_region);
    observe_after_reset("reset-write", write_offset, old_write, new_write, write_region);
    `uvm_info({tag_prefix, "_RESET"}, $sformatf("OBSERVATION %s contents after reset: read span %s; write span %s (new = the interrupted write's data)", bridge_name, read_region, write_region), UVM_LOW)

    post_reset_checks(target_ok);
    fresh_words = new[RESET_BEATS];
    foreach (fresh_words[beat]) fresh_words[beat] = $urandom();
    request = build_write("after-reset", fresh_offset, fresh_words);
    issue_request(request);
    passed = target_ok && check_okay(request);
    request = build_read("after-reset", fresh_offset, RESET_BEATS);
    issue_request(request);
    passed &= check_read_words(request, fresh_words);
    reset_passed = passed && violations == 0;
    `uvm_info({tag_prefix, "_RESET"}, $sformatf("%s %s: VALIDs LOW during reset=%s; post-reset checks and INCR-%0d write/read after reset=%s", reset_passed ? "PASS" : "FAIL", bridge_name, violations == 0 ? "yes" : "no", RESET_BEATS, passed ? "OKAY, data matched" : "failed"), UVM_LOW)
  endtask
endclass
