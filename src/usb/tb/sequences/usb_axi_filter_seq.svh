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
// Directed evaluation of the AXI USER filter on all four wrapper converters.
// Each paths[] row is one converter: COMBO (DEV0 CSR) and DEV0 SRAM use the
// Combo policy; DEV1 CSR and DEV1 SRAM use the DEV1 policy. HUB shares the
// COMBO filter and is not exercised.
//
//   P0 Program random disjoint allowlists, validate chosen USERs, save route words.
//   P1 Bypass: both enables low, a nonmember USER succeeds on every path.
//   P2 Allow: both enables high, allowlisted USERs succeed.
//   P3 Deny: an opposite-device USER gets SLVERR; write does not land; read is zero.
//   P4 Recovery: allowed traffic succeeds again with filtering still enabled.
//   P5 Exact match: flipping the USER MSB of a member is denied (CSR paths).
//   P6 Independent enables: only the bypassed policy accepts a nonmember.
//   P7 Rejected bursts: with both policies enabled, a nonmember sends 10 FIXED
//      and 10 INCR read and write bursts per path (min and max lengths included),
//      mixed 2:1:1 with allowed single-beat reads and writes. Each burst gets
//      SLVERR (reads: every beat, zero data). Storage is not read after each
//      rejected write; RTL reject-state assertions check the AHB side.
//   P8 Accepted SRAM bursts: with both policies enabled, each SRAM path runs 10
//      own-USER INCR burst writes, each followed by a burst read of the same
//      range that must return OKAY and the written data on every beat. Lengths
//      include 2, 16, 17, and 256; starts are random in local scratch offsets
//      0x1000-0x1FFF so word 0 is untouched.
//   P9 Restore route words with filtering bypassed; final readback on every path.
//   P10 Require every P7 bucket, the P8 pairs, and exact per-target totals,
//       then set completed.
//
// shadow[] holds the last value accepted on each path; every preservation
// check compares against it. Allowlist USERs are random and are not stored in
// the sequence: they are read back from the control VIF when needed. Policy
// signals change only with nonblocking assignments at a clk rising edge, and
// only between blocking transfers.
class usb_axi_filter_seq extends usb_base_seq;
  `uvm_object_utils(usb_axi_filter_seq)

  // One filtered AXI path. Its USERs come from the allowlist ports: CSR paths
  // use entry 0 and SRAM paths the last entry, so both ends of each list are used.
  typedef struct {
    usb_target_e target;
    bit combo_policy; // 1: guarded by the Combo policy; 0: by DEV1
    bit is_csr;       // route register path; also gets the near-miss check
    logic [31:0] offset;
    logic [31:0] mask;
  } filter_path_t;

  localparam int unsigned FILTER_PATH_COUNT = 4;
  localparam logic [31:0] SRAM_WORD_ADDR = 32'h0;
  localparam bit OWN_LIST = 1'b1;
  localparam bit OTHER_LIST = 1'b0;
  localparam usb_axi_user_t USER_MSB = usb_axi_user_t'(1) << (USB_TB_AXI_USER_WIDTH - 1);
  // The patterns differ in bits 31:30 and the low bits, so they stay distinct under both route masks.
  localparam logic [31:0] PATTERN_A = 32'h4000_a55a;
  localparam logic [31:0] PATTERN_B = 32'h8000_5aa5;

  // P7 rejected-burst buckets, quotas, and burst-length limits (AXI4: FIXED <= 16, INCR <= 256 beats).
  typedef enum int unsigned {
    BURST_FIXED_READ,
    BURST_FIXED_WRITE,
    BURST_INCR_READ,
    BURST_INCR_WRITE
  } burst_bucket_e;
  typedef enum int unsigned {
    P7_REJECTED_BURST,
    P7_ALLOWED_READ,
    P7_ALLOWED_WRITE
  } p7_operation_e;
  localparam int unsigned BURST_BUCKET_COUNT = 4;
  localparam int unsigned BURSTS_PER_BUCKET = 10;
  localparam int unsigned P7_MAX_OPS_PER_PATH = 1000;
  localparam int unsigned BURST_MIN_BEATS = 2;
  localparam int unsigned BURST_FIXED_MAX_BEATS = 16;
  localparam int unsigned BURST_CSR_INCR_MAX_BEATS = 16;
  localparam int unsigned BURST_SRAM_INCR_MAX_BEATS = 256;

  // P8 accepted SRAM INCR bursts: write/readback pairs in a local scratch page
  // that avoids word 0 (shadow[]). Every path must also hit each required length.
  localparam int unsigned P8_PAIRS_PER_PATH = 10;
  localparam logic [31:0] P8_WINDOW_BASE = 32'h1000;
  localparam int unsigned P8_WINDOW_WORDS = 1024;
  localparam int unsigned P8_REQUIRED_LENGTH_COUNT = 4;
  localparam int unsigned P8_REQUIRED_LENGTHS[P8_REQUIRED_LENGTH_COUNT] = '{2, 16, 17, 256};

  bit completed;
  filter_path_t paths[FILTER_PATH_COUNT] = '{
    '{target: USB_DEV0_CSR,  combo_policy: 1'b1, is_csr: 1'b1, offset: '0,                mask: USB_DEV0_ROUTE_MASK},
    '{target: USB_DEV0_SRAM, combo_policy: 1'b1, is_csr: 1'b0, offset: SRAM_WORD_ADDR,    mask: 32'hffff_ffff},
    '{target: USB_DEV1_CSR,  combo_policy: 1'b0, is_csr: 1'b1, offset: '0,                mask: USB_DEV1_ROUTE_MASK},
    '{target: USB_DEV1_SRAM, combo_policy: 1'b0, is_csr: 1'b0, offset: SRAM_WORD_ADDR,    mask: 32'hffff_ffff}
  };
  // Random USER in neither allowlist; the only USER not observable on the control VIF.
  usb_axi_user_t nonmember_user;
  logic [31:0] shadow[USB_TARGET_COUNT];
  int unsigned denied_writes[USB_TARGET_COUNT];
  int unsigned denied_reads[USB_TARGET_COUNT];
  // P7 per-path bucket counts and the shortest/longest burst sent in each bucket.
  int unsigned burst_counts[FILTER_PATH_COUNT][BURST_BUCKET_COUNT];
  int unsigned burst_min_beats[FILTER_PATH_COUNT][BURST_BUCKET_COUNT];
  int unsigned burst_max_beats[FILTER_PATH_COUNT][BURST_BUCKET_COUNT];
  int unsigned p7_operations[FILTER_PATH_COUNT];
  // P7 allowed single-beat traffic, counted when the operation is chosen.
  int unsigned p7_allowed_reads[USB_TARGET_COUNT];
  int unsigned p7_allowed_writes[USB_TARGET_COUNT];
  // P8 counts, updated only after each response or data check passes.
  int unsigned p8_burst_writes[USB_TARGET_COUNT];
  int unsigned p8_burst_reads[USB_TARGET_COUNT];
  int unsigned p8_pairs[USB_TARGET_COUNT];
  int unsigned p8_checked_words[USB_TARGET_COUNT];
  int unsigned p8_pair_beats[USB_TARGET_COUNT];
  bit p8_length_hit[USB_TARGET_COUNT][P8_REQUIRED_LENGTH_COUNT];
  time p8_max_256_write[USB_TARGET_COUNT];
  time p8_max_256_read[USB_TARGET_COUNT];
  string phase_name;

  // Create the sequence. Counters and shadow values are cleared in body().
  function new(string name = "usb_axi_filter_seq");
    super.new(name);
  endfunction

  // Extend the base handle check: require both filter policies to still hold
  // their known-low bypass default, and resolve each CSR path's route-register
  // offset from the RAL.
  virtual task pre_start();
    super.pre_start();
    check_axi_user_filters_bypassed();
    foreach (paths[index]) begin
      if (paths[index].is_csr) paths[index].offset = csr_offset(paths[index].target, "INTROUTE");
    end
  endtask

  // ---------------------------------------------------------------------------
  // Policy control
  // ---------------------------------------------------------------------------

  // Begin a scenario phase: record its label for failure messages, log the
  // checkpoint, and set both filter enables. The caller must have no transfer
  // in flight (every access task here is blocking).
  protected task start_phase(string name, string description, bit combo_enable, bit dev1_enable);
    phase_name = name;
    `uvm_info("USB_FILTER_SEQ", $sformatf("[%s] Starting with combo_enable=%0b dev1_enable=%0b: %s", phase_name, combo_enable, dev1_enable, description), UVM_LOW)
    set_axi_user_filter_enables(combo_enable, dev1_enable);
  endtask

  // Randomize every entry of both allowlists and nonmember_user, then drive
  // and confirm both lists. All values are unique across both lists and the
  // nonmember, and no entry's MSB-flipped value is in its own list. Logs the
  // lists as the DUT sees them.
  protected task program_allowlists();
    usb_combo_allowlist_t combo_users;
    usb_dev1_allowlist_t dev1_users;

    if (!std::randomize(combo_users, dev1_users, nonmember_user) with {
          unique {combo_users, dev1_users, nonmember_user};
          foreach (combo_users[index]) !((combo_users[index] ^ USER_MSB) inside {combo_users});
          foreach (dev1_users[index]) !((dev1_users[index] ^ USER_MSB) inside {dev1_users});
        }) begin
      `uvm_fatal("USB_FILTER_SEQ", "Unable to randomize the AXI USER allowlists")
    end
    set_axi_user_allowlists(combo_users, dev1_users);
    `uvm_info("USB_FILTER_SEQ", $sformatf("[%s] Allowlists programmed: %s; nonmember=0x%08h", phase_name, format_axi_user_allowlists(), nonmember_user), UVM_LOW)
  endtask

  // Return a USER read from the allowlist signals on the control VIF: from the
  // path's own list (OWN_LIST) or the other device's list (OTHER_LIST), at the
  // path's position (entry 0 for CSR paths, last entry for SRAM paths).
  protected function usb_axi_user_t path_user(filter_path_t path, bit own_list);
    bit combo_list;

    combo_list = own_list ? path.combo_policy : !path.combo_policy;
    if (path.is_csr) return axi_user_allowlist_entry(combo_list, 0);
    return axi_user_allowlist_entry(combo_list, (combo_list ? USB_COMBO_NUM_PRIV_AXI_USERS : USB_DEV1_NUM_PRIV_AXI_USERS) - 1);
  endfunction

  // Fatal if a chosen USER would not exercise the intended decision on the
  // lists the DUT sees: the nonmember must be in neither list, and each path's
  // opposite and MSB-flipped (CSR only) USERs must be absent from its own list.
  protected function void check_user_choices();
    if (axi_user_in_allowlist(1'b1, nonmember_user) || axi_user_in_allowlist(1'b0, nonmember_user)) begin
      `uvm_fatal("USB_FILTER_SEQ", $sformatf("Nonmember USER 0x%0h is present in an allowlist", nonmember_user))
    end
    foreach (paths[index]) begin
      filter_path_t path = paths[index];
      usb_axi_user_t opposite_user = path_user(path, OTHER_LIST);
      usb_axi_user_t near_miss_user = path_user(path, OWN_LIST) ^ USER_MSB;

      if (axi_user_in_allowlist(path.combo_policy, opposite_user)) begin
        `uvm_fatal("USB_FILTER_SEQ", $sformatf("%s opposite USER 0x%0h is present in its own allowlist", usb_target_name(path.target), opposite_user))
      end
      if (path.is_csr && axi_user_in_allowlist(path.combo_policy, near_miss_user)) begin
        `uvm_fatal("USB_FILTER_SEQ", $sformatf("%s near-miss USER 0x%0h is present in its own allowlist", usb_target_name(path.target), near_miss_user))
      end
    end
    `uvm_info("USB_FILTER_SEQ", $sformatf("[%s] USER choices validated against the driven allowlists", phase_name), UVM_LOW)
  endfunction

  // ---------------------------------------------------------------------------
  // Checked accesses
  // ---------------------------------------------------------------------------

  // Return the pattern that differs from the path's last accepted value, so the
  // next write is observable whether it is accepted or must be blocked.
  protected function logic [31:0] next_pattern(filter_path_t path);
    return (shadow[path.target] === PATTERN_A) ? PATTERN_B : PATTERN_A;
  endfunction

  // Read the path with user; require OKAY and the last accepted value under the
  // path's mask. Counts one read and one comparison in target_stats.
  protected task expect_stored(filter_path_t path, usb_axi_user_t user);
    expect32(path.target, path.offset, shadow[path.target], path.mask, usb_axi_user_override::with_value(user));
  endtask

  // Require user to be accepted on the path: write next_pattern() expecting
  // OKAY, record it in shadow[], then read it back with the same USER.
  protected task expect_accept(filter_path_t path, usb_axi_user_t user);
    logic [31:0] data;

    data = next_pattern(path);
    write32(path.target, path.offset, data, usb_axi_user_override::with_value(user));
    shadow[path.target] = data;
    expect_stored(path, user);
  endtask

  // Write next_pattern() with user and require a locally generated SLVERR.
  // shadow[] and the base success counters are left unchanged.
  protected task deny_write(filter_path_t path, usb_axi_user_t user);
    aaxi_master_tr transaction;
    logic [31:0] data;

    data = next_pattern(path);
    check_address(path.target, path.offset);
    transaction = create_transaction(path.target, path.offset, 1'b1, data, usb_axi_user_override::with_value(user));
    `uvm_info("USB_FILTER_ACCESS", $sformatf("[%s] Start denied %s write offset=0x%08h data=0x%08h user=0x%0h", phase_name, usb_target_name(path.target), path.offset, data, user), UVM_LOW)
    execute_transaction(path.target, 32'(transaction.addr), 1'b1, transaction);
    if (transaction.resp !== AAXI_RESP_SLVERR) begin
      `uvm_fatal("USB_FILTER_RESPONSE", $sformatf("[%s] %s write offset=0x%08h user=0x%0h response=0x%0h, expected SLVERR", phase_name, usb_target_name(path.target), path.offset, user, transaction.resp))
    end
    denied_writes[path.target]++;
  endtask

  // Read with user and require exactly one SLVERR beat carrying a full,
  // known-zero data word. unpack_read_data() is not used because it requires OKAY.
  protected task deny_read(filter_path_t path, usb_axi_user_t user);
    aaxi_master_tr transaction;

    check_address(path.target, path.offset);
    transaction = create_transaction(path.target, path.offset, 1'b0, '0, usb_axi_user_override::with_value(user));
    `uvm_info("USB_FILTER_ACCESS", $sformatf("[%s] Start denied %s read offset=0x%08h user=0x%0h", phase_name, usb_target_name(path.target), path.offset, user), UVM_LOW)
    execute_transaction(path.target, 32'(transaction.addr), 1'b0, transaction);
    if (transaction.rresp_Q.size() != 1 || transaction.data.size() != USB_AXI_DATA_WIDTH / 8) begin
      `uvm_fatal("USB_FILTER_RESPONSE", $sformatf("[%s] %s read offset=0x%08h user=0x%0h returned %0d responses and %0d bytes, expected 1 and %0d", phase_name, usb_target_name(path.target), path.offset, user, transaction.rresp_Q.size(), transaction.data.size(), USB_AXI_DATA_WIDTH / 8))
    end
    if (transaction.rresp_Q[0] !== AAXI_RESP_SLVERR) begin
      `uvm_fatal("USB_FILTER_RESPONSE", $sformatf("[%s] %s read offset=0x%08h user=0x%0h response=0x%0h, expected SLVERR", phase_name, usb_target_name(path.target), path.offset, user, transaction.rresp_Q[0]))
    end
    foreach (transaction.data[byte_index]) begin
      if (transaction.data[byte_index] !== 8'h00) begin
        `uvm_fatal("USB_FILTER_DATA", $sformatf("[%s] %s denied read offset=0x%08h user=0x%0h byte%0d=0x%0h, expected 0x00", phase_name, usb_target_name(path.target), path.offset, user, byte_index, transaction.data[byte_index]))
      end
    end
    denied_reads[path.target]++;
  endtask

  // Require user to be rejected on the path: a denied write, then a read with
  // the path's own allowlisted USER proving the write did not reach storage,
  // then a denied read.
  protected task expect_deny(filter_path_t path, usb_axi_user_t user);
    deny_write(path, user);
    expect_stored(path, path_user(path, OWN_LIST));
    deny_read(path, user);
  endtask

  // ---------------------------------------------------------------------------
  // Rejected bursts (P7)
  // ---------------------------------------------------------------------------

  // Return 1 for the write buckets.
  protected function bit bucket_is_write(burst_bucket_e bucket);
    return bucket inside {BURST_FIXED_WRITE, BURST_INCR_WRITE};
  endfunction

  // Return 1 for the FIXED buckets.
  protected function bit bucket_is_fixed(burst_bucket_e bucket);
    return bucket inside {BURST_FIXED_READ, BURST_FIXED_WRITE};
  endfunction

  // Return the longest legal burst for the bucket on this path. Only SRAM INCR
  // bursts use the AXI4 256-beat limit; the CSR window holds 16 words.
  protected function int unsigned bucket_max_beats(filter_path_t path, burst_bucket_e bucket);
    if (bucket_is_fixed(bucket)) return BURST_FIXED_MAX_BEATS;
    return path.is_csr ? BURST_CSR_INCR_MAX_BEATS : BURST_SRAM_INCR_MAX_BEATS;
  endfunction

  // Return the burst's first local byte offset. CSR INCR bursts end at the route
  // word when possible and otherwise start at 0; the subtraction is guarded
  // against unsigned underflow. SRAM bursts start at 0.
  protected function logic [31:0] burst_start_offset(filter_path_t path, burst_bucket_e bucket, int unsigned beats);
    int unsigned span;

    if (!path.is_csr) return SRAM_WORD_ADDR;
    if (bucket_is_fixed(bucket)) return path.offset;
    span = 4 * (beats - 1);
    return (span >= path.offset) ? 32'h0 : path.offset - span;
  endfunction

  // Send one multi-beat 32-bit FIXED or INCR burst from nonmember_user and
  // require local rejection: a write gets SLVERR; a read returns one SLVERR,
  // zero-data beat per requested beat. Counts one denial per burst and never
  // updates shadow[]. Storage is not read back here; rejected-write leakage is
  // covered only by the bridge's reject-state assertions.
  protected task send_rejected_burst(filter_path_t path, burst_bucket_e bucket, int unsigned beats);
    aaxi_master_tr transaction;
    bit is_write;
    bit is_fixed;
    logic [31:0] start_offset;
    logic [31:0] last_offset;
    logic [31:0] data;
    logic [63:0] first_byte;
    logic [63:0] last_byte;
    string label;

    is_write = bucket_is_write(bucket);
    is_fixed = bucket_is_fixed(bucket);
    start_offset = burst_start_offset(path, bucket, beats);
    last_offset = is_fixed ? start_offset : start_offset + 4 * (beats - 1);
    data = is_write ? next_pattern(path) : '0;
    label = $sformatf("[%s] %s %s beats=%0d offset=0x%08h..0x%08h user=0x%0h", phase_name, usb_target_name(path.target), bucket.name(), beats, start_offset, last_offset, nonmember_user);
    // Logged first so address-check and timeout fatals in the base helpers have full context.
    `uvm_info("USB_FILTER_ACCESS", {"Start rejected burst ", label}, UVM_LOW)
    if (beats < BURST_MIN_BEATS || beats > bucket_max_beats(path, bucket)) begin
      `uvm_fatal("USB_FILTER_BURST", {"Illegal burst length ", label})
    end
    check_address(path.target, start_offset);
    check_address(path.target, last_offset);

    transaction = create_transaction(path.target, start_offset, is_write, data, usb_axi_user_override::with_value(nonmember_user));
    first_byte = 64'(transaction.addr);
    last_byte = first_byte + 64'(last_offset - start_offset) + 64'd3;
    if (first_byte[63:12] !== last_byte[63:12]) begin
      `uvm_fatal("USB_FILTER_BURST", $sformatf("%s crosses a 4 KB boundary: bus 0x%0h..0x%0h", label, first_byte, last_byte))
    end
    transaction.len = beats - 1;
    transaction.size = 2;
    if (is_fixed) transaction.burst = AAXI_BURST_FIXED;
    else transaction.burst = AAXI_BURST_INCR;
    if (is_write) begin
      transaction.data.delete();
      transaction.strobes.delete();
      transaction.wuser_A = new[beats];
      for (int unsigned beat = 0; beat < beats; beat++) begin
        for (int unsigned byte_index = 0; byte_index < USB_AXI_DATA_WIDTH / 8; byte_index++) begin
          transaction.data.push_back(data[byte_index * 8 +: 8]);
          transaction.strobes.push_back(1'b1);
        end
        transaction.wuser_A[beat] = nonmember_user;
      end
    end

    execute_transaction(path.target, 32'(transaction.addr), is_write, transaction);
    if (is_write) begin
      if (transaction.resp !== AAXI_RESP_SLVERR) begin
        `uvm_fatal("USB_FILTER_RESPONSE", $sformatf("%s write response=0x%0h, expected SLVERR", label, transaction.resp))
      end
      denied_writes[path.target]++;
    end else begin
      if (transaction.rresp_Q.size() != beats || transaction.data.size() != beats * (USB_AXI_DATA_WIDTH / 8)) begin
        `uvm_fatal("USB_FILTER_RESPONSE", $sformatf("%s read returned %0d responses and %0d bytes, expected %0d and %0d", label, transaction.rresp_Q.size(), transaction.data.size(), beats, beats * (USB_AXI_DATA_WIDTH / 8)))
      end
      foreach (transaction.rresp_Q[beat]) begin
        if (transaction.rresp_Q[beat] !== AAXI_RESP_SLVERR) begin
          `uvm_fatal("USB_FILTER_RESPONSE", $sformatf("%s read beat%0d response=0x%0h, expected SLVERR", label, beat, transaction.rresp_Q[beat]))
        end
      end
      foreach (transaction.data[byte_index]) begin
        if (transaction.data[byte_index] !== 8'h00) begin
          `uvm_fatal("USB_FILTER_DATA", $sformatf("%s read byte%0d=0x%0h, expected 0x00", label, byte_index, transaction.data[byte_index]))
        end
      end
      denied_reads[path.target]++;
    end
  endtask

  // Return 1 when the bucket's shortest and longest legal lengths were both sent.
  protected function bit bucket_bounds_hit(int unsigned path_index, burst_bucket_e bucket);
    return burst_counts[path_index][bucket] != 0 && burst_min_beats[path_index][bucket] == BURST_MIN_BEATS &&
           burst_max_beats[path_index][bucket] == bucket_max_beats(paths[path_index], bucket);
  endfunction

  // Log one USB_FILTER_BURST_SUMMARY line for a path: per-bucket count, length
  // range, and boundary coverage, plus allowed traffic and total operations.
  protected function void report_burst_path(int unsigned path_index);
    filter_path_t path = paths[path_index];
    string text;

    for (int bucket_index = 0; bucket_index < BURST_BUCKET_COUNT; bucket_index++) begin
      burst_bucket_e bucket = burst_bucket_e'(bucket_index);
      string bounds_text = bucket_bounds_hit(path_index, bucket) ? "hit" : "MISSING";

      text = {text, $sformatf(" %s=%0d/%0d beats=%0d..%0d bounds=%s;", bucket.name(), burst_counts[path_index][bucket], BURSTS_PER_BUCKET, burst_min_beats[path_index][bucket], burst_max_beats[path_index][bucket], bounds_text)};
    end
    `uvm_info("USB_FILTER_BURST_SUMMARY", $sformatf("[%s] %s:%s allowed r/w=%0d/%0d ops=%0d (cap %0d)", phase_name, usb_target_name(path.target), text, p7_allowed_reads[path.target], p7_allowed_writes[path.target], p7_operations[path_index], P7_MAX_OPS_PER_PATH), UVM_LOW)
  endfunction

  // Run P7 on one path: until every bucket holds BURSTS_PER_BUCKET rejected
  // bursts, pick rejected burst / allowed read / allowed write with weights
  // 2:1:1. Each iteration sends exactly one transfer. The first two bursts in a
  // bucket use its minimum then maximum length; later lengths are random.
  protected task run_burst_path(int unsigned path_index);
    filter_path_t path = paths[path_index];
    usb_axi_user_t own_user = path_user(path, OWN_LIST);
    burst_bucket_e open_buckets[$];
    burst_bucket_e bucket;
    p7_operation_e operation;
    int unsigned beats;
    logic [31:0] data;

    for (int bucket_index = 0; bucket_index < BURST_BUCKET_COUNT; bucket_index++) begin
      burst_counts[path_index][bucket_index] = 0;
      burst_min_beats[path_index][bucket_index] = 0;
      burst_max_beats[path_index][bucket_index] = 0;
    end
    p7_allowed_reads[path.target] = 0;
    p7_allowed_writes[path.target] = 0;
    p7_operations[path_index] = 0;
    `uvm_info("USB_FILTER_SEQ", $sformatf("[%s] %s: starting %0d rejected bursts per bucket, own USER=0x%0h nonmember=0x%0h", phase_name, usb_target_name(path.target), BURSTS_PER_BUCKET, own_user, nonmember_user), UVM_LOW)

    forever begin
      open_buckets.delete();
      for (int bucket_index = 0; bucket_index < BURST_BUCKET_COUNT; bucket_index++) begin
        if (burst_counts[path_index][bucket_index] < BURSTS_PER_BUCKET) open_buckets.push_back(burst_bucket_e'(bucket_index));
      end
      if (open_buckets.size() == 0) break;
      p7_operations[path_index]++;
      if (p7_operations[path_index] > P7_MAX_OPS_PER_PATH) begin
        report_burst_path(path_index);
        `uvm_fatal("USB_FILTER_BURST", $sformatf("[%s] %s exceeded %0d operations with %0d bucket(s) unfilled", phase_name, usb_target_name(path.target), P7_MAX_OPS_PER_PATH, open_buckets.size()))
      end

      randcase
        2: operation = P7_REJECTED_BURST;
        1: operation = P7_ALLOWED_READ;
        1: operation = P7_ALLOWED_WRITE;
      endcase

      case (operation)
        P7_REJECTED_BURST: begin
          bucket = open_buckets[$urandom_range(open_buckets.size() - 1)];
          case (burst_counts[path_index][bucket])
            0:       beats = BURST_MIN_BEATS;
            1:       beats = bucket_max_beats(path, bucket);
            default: beats = $urandom_range(bucket_max_beats(path, bucket), BURST_MIN_BEATS);
          endcase
          send_rejected_burst(path, bucket, beats);
          if (burst_counts[path_index][bucket] == 0 || beats < burst_min_beats[path_index][bucket]) burst_min_beats[path_index][bucket] = beats;
          if (beats > burst_max_beats[path_index][bucket]) burst_max_beats[path_index][bucket] = beats;
          burst_counts[path_index][bucket]++;
        end
        P7_ALLOWED_READ: begin
          expect_stored(path, own_user);
          p7_allowed_reads[path.target]++;
        end
        P7_ALLOWED_WRITE: begin
          data = next_pattern(path);
          write32(path.target, path.offset, data, usb_axi_user_override::with_value(own_user));
          shadow[path.target] = data;
          p7_allowed_writes[path.target]++;
        end
        default: `uvm_fatal("USB_FILTER_BURST", $sformatf("[%s] Invalid P7 operation %0d", phase_name, operation))
      endcase
    end
    report_burst_path(path_index);
  endtask

  // Run P7 on every path in order, then log the phase totals.
  protected task run_burst_phase();
    int unsigned total_bursts;
    string text;

    foreach (paths[index]) run_burst_path(index);
    foreach (paths[index]) begin
      int unsigned path_bursts = 0;

      for (int bucket_index = 0; bucket_index < BURST_BUCKET_COUNT; bucket_index++) path_bursts += burst_counts[index][bucket_index];
      total_bursts += path_bursts;
      text = {text, $sformatf(" %s bursts=%0d r/w=%0d/%0d ops=%0d;", usb_target_name(paths[index].target), path_bursts, p7_allowed_reads[paths[index].target], p7_allowed_writes[paths[index].target], p7_operations[index])};
    end
    `uvm_info("USB_FILTER_BURST_SUMMARY", $sformatf("[%s] Complete: %0d/%0d rejected bursts;%s", phase_name, total_bursts, FILTER_PATH_COUNT * BURST_BUCKET_COUNT * BURSTS_PER_BUCKET, text), UVM_LOW)
  endtask

  // ---------------------------------------------------------------------------
  // Accepted SRAM bursts (P8)
  // ---------------------------------------------------------------------------

  // Return a context string for P8 start, completion, and failure messages.
  protected function string accepted_burst_label(filter_path_t path, logic [31:0] offset, int unsigned beats, bit is_write, int unsigned pair_index);
    return $sformatf("[%s] %s pair %0d/%0d INCR %s beats=%0d offset=0x%08h..0x%08h user=0x%0h", phase_name, usb_target_name(path.target), pair_index + 1, P8_PAIRS_PER_PATH, is_write ? "write" : "read", beats, offset, offset + 32'(4 * (beats - 1)), path_user(path, OWN_LIST));
  endfunction

  // Build, but do not send, one 32-bit INCR burst on an SRAM path with the
  // path's own USER. Validates the target, length, window, target bounds, and
  // 4 KB page before packing. Writes carry data_q least-significant byte first
  // with every strobe set; reads leave the request data queue empty.
  protected function aaxi_master_tr create_accepted_burst(filter_path_t path, logic [31:0] offset, int unsigned beats, bit is_write, logic [31:0] data_q[$], string label);
    aaxi_master_tr transaction;
    usb_axi_user_t own_user;
    logic [31:0] last_offset;
    logic [63:0] first_byte;
    logic [63:0] last_byte;

    if (path.is_csr) begin
      `uvm_fatal("USB_FILTER_P8", {"Accepted bursts are limited to SRAM paths ", label})
    end
    if (beats < BURST_MIN_BEATS || beats > BURST_SRAM_INCR_MAX_BEATS || data_q.size() != beats) begin
      `uvm_fatal("USB_FILTER_P8", $sformatf("%s has %0d data words; expected %0d beats in %0d..%0d", label, data_q.size(), beats, BURST_MIN_BEATS, BURST_SRAM_INCR_MAX_BEATS))
    end
    last_offset = offset + 32'(4 * (beats - 1));
    if (offset < P8_WINDOW_BASE || 64'(last_offset) + 64'd3 >= 64'(P8_WINDOW_BASE) + 64'(4 * P8_WINDOW_WORDS)) begin
      `uvm_fatal("USB_FILTER_P8", {"Burst leaves the P8 scratch window ", label})
    end
    check_address(path.target, offset);
    check_address(path.target, last_offset);

    own_user = path_user(path, OWN_LIST);
    transaction = create_transaction(path.target, offset, is_write, is_write ? data_q[0] : '0, usb_axi_user_override::with_value(own_user));
    first_byte = 64'(transaction.addr);
    last_byte = first_byte + 64'(4 * beats) - 64'd1;
    if (first_byte[63:12] !== last_byte[63:12]) begin
      `uvm_fatal("USB_FILTER_P8", $sformatf("%s crosses a 4 KB boundary: bus 0x%0h..0x%0h", label, first_byte, last_byte))
    end
    transaction.len = beats - 1;
    transaction.size = 2;
    transaction.burst = AAXI_BURST_INCR;
    if (is_write) begin
      transaction.data.delete();
      transaction.strobes.delete();
      transaction.wuser_A = new[beats];
      for (int unsigned beat = 0; beat < beats; beat++) begin
        for (int unsigned byte_index = 0; byte_index < USB_AXI_DATA_WIDTH / 8; byte_index++) begin
          transaction.data.push_back(data_q[beat][byte_index * 8 +: 8]);
          transaction.strobes.push_back(1'b1);
        end
        transaction.wuser_A[beat] = own_user;
      end
    end
    return transaction;
  endfunction

  // Send one accepted INCR burst write and require OKAY. Counts the write in
  // target_stats and p8_burst_writes only after the response passes, and
  // records the transfer time for 256-beat bursts.
  protected task accepted_burst_write(filter_path_t path, logic [31:0] offset, logic [31:0] data_q[$], int unsigned pair_index);
    aaxi_master_tr transaction;
    int unsigned beats = data_q.size();
    string label = accepted_burst_label(path, offset, beats, 1'b1, pair_index);
    time start_time;
    time elapsed;

    // Logged first so address-check and timeout fatals in the base helpers have full context.
    `uvm_info("USB_FILTER_ACCESS", {"Start accepted burst ", label}, UVM_LOW)
    transaction = create_accepted_burst(path, offset, beats, 1'b1, data_q, label);
    start_time = $time;
    execute_transaction(path.target, 32'(transaction.addr), 1'b1, transaction);
    elapsed = $time - start_time;
    if (transaction.resp !== AAXI_RESP_OKAY) begin
      `uvm_fatal("USB_FILTER_RESPONSE", $sformatf("%s write response=0x%0h, expected OKAY", label, transaction.resp))
    end
    target_stats[path.target].writes++;
    p8_burst_writes[path.target]++;
    if (beats == BURST_SRAM_INCR_MAX_BEATS && elapsed > p8_max_256_write[path.target]) p8_max_256_write[path.target] = elapsed;
    `uvm_info("USB_FILTER_ACCESS", $sformatf("Completed accepted burst %s in %0t", label, elapsed), UVM_LOW)
  endtask

  // Send one accepted INCR burst read and require one OKAY response and one
  // exact 32-bit word per beat, compared without masking against data_q.
  // Counts the read, one comparison, and the checked words only after every
  // beat passes, and records the transfer time for 256-beat bursts.
  protected task accepted_burst_read_check(filter_path_t path, logic [31:0] offset, logic [31:0] data_q[$], int unsigned pair_index);
    aaxi_master_tr transaction;
    int unsigned beats = data_q.size();
    string label = accepted_burst_label(path, offset, beats, 1'b0, pair_index);
    logic [31:0] actual;
    time start_time;
    time elapsed;

    `uvm_info("USB_FILTER_ACCESS", {"Start accepted burst ", label}, UVM_LOW)
    transaction = create_accepted_burst(path, offset, beats, 1'b0, data_q, label);
    start_time = $time;
    execute_transaction(path.target, 32'(transaction.addr), 1'b0, transaction);
    elapsed = $time - start_time;
    if (transaction.rresp_Q.size() != beats || transaction.data.size() != beats * (USB_AXI_DATA_WIDTH / 8)) begin
      `uvm_fatal("USB_FILTER_RESPONSE", $sformatf("%s returned %0d responses and %0d bytes, expected %0d and %0d", label, transaction.rresp_Q.size(), transaction.data.size(), beats, beats * (USB_AXI_DATA_WIDTH / 8)))
    end
    for (int unsigned beat = 0; beat < beats; beat++) begin
      if (transaction.rresp_Q[beat] !== AAXI_RESP_OKAY) begin
        `uvm_fatal("USB_FILTER_RESPONSE", $sformatf("%s beat %0d response=0x%0h, expected OKAY", label, beat, transaction.rresp_Q[beat]))
      end
      for (int unsigned byte_index = 0; byte_index < USB_AXI_DATA_WIDTH / 8; byte_index++) begin
        actual[byte_index * 8 +: 8] = transaction.data[beat * (USB_AXI_DATA_WIDTH / 8) + byte_index];
      end
      if (actual !== data_q[beat]) begin
        `uvm_fatal("USB_FILTER_DATA", $sformatf("%s beat %0d offset=0x%08h expected=0x%08h actual=0x%08h", label, beat, offset + 32'(4 * beat), data_q[beat], actual))
      end
    end
    target_stats[path.target].reads++;
    target_stats[path.target].comparisons++;
    p8_burst_reads[path.target]++;
    p8_checked_words[path.target] += beats;
    if (beats == BURST_SRAM_INCR_MAX_BEATS && elapsed > p8_max_256_read[path.target]) p8_max_256_read[path.target] = elapsed;
    `uvm_info("USB_FILTER_ACCESS", $sformatf("Completed accepted burst %s in %0t; all %0d words matched", label, elapsed, beats), UVM_LOW)
  endtask

  // Return 1 when every required P8 length completed a checked pair on target.
  protected function bit p8_lengths_hit(usb_target_e target);
    for (int length_index = 0; length_index < P8_REQUIRED_LENGTH_COUNT; length_index++) begin
      if (!p8_length_hit[target][length_index]) return 1'b0;
    end
    return 1'b1;
  endfunction

  // Run P8 on one SRAM path: the required lengths plus random ones in shuffled
  // order, each as a random-data burst write followed by a checked read of the
  // same range at a random aligned start inside the scratch window. A pair
  // counts only after its read comparison passes.
  protected task run_accepted_burst_path(filter_path_t path);
    int unsigned lengths[$];
    int unsigned beats;
    int unsigned word_index;
    logic [31:0] offset;
    logic [31:0] data_q[$];
    string length_text;
    string hit_text;

    foreach (P8_REQUIRED_LENGTHS[length_index]) lengths.push_back(P8_REQUIRED_LENGTHS[length_index]);
    while (lengths.size() < P8_PAIRS_PER_PATH) begin
      if (!std::randomize(beats) with { beats inside {[BURST_MIN_BEATS:BURST_SRAM_INCR_MAX_BEATS]}; }) begin
        `uvm_fatal("USB_FILTER_P8", $sformatf("[%s] Unable to randomize a burst length", phase_name))
      end
      lengths.push_back(beats);
    end
    lengths.shuffle();
    foreach (lengths[pair_index]) length_text = {length_text, $sformatf(" %0d", lengths[pair_index])};
    `uvm_info("USB_FILTER_SEQ", $sformatf("[%s] %s: starting %0d accepted INCR write/read pairs, user=0x%0h, beats:%s", phase_name, usb_target_name(path.target), P8_PAIRS_PER_PATH, path_user(path, OWN_LIST), length_text), UVM_LOW)

    foreach (lengths[pair_index]) begin
      beats = lengths[pair_index];
      if (!std::randomize(word_index) with { word_index <= P8_WINDOW_WORDS - beats; }) begin
        `uvm_fatal("USB_FILTER_P8", $sformatf("[%s] Unable to randomize a start for %0d beats", phase_name, beats))
      end
      offset = P8_WINDOW_BASE + 32'(4 * word_index);
      data_q.delete();
      for (int unsigned beat = 0; beat < beats; beat++) data_q.push_back($urandom());

      accepted_burst_write(path, offset, data_q, pair_index);
      accepted_burst_read_check(path, offset, data_q, pair_index);
      p8_pairs[path.target]++;
      p8_pair_beats[path.target] += beats;
      foreach (P8_REQUIRED_LENGTHS[length_index]) begin
        if (beats == P8_REQUIRED_LENGTHS[length_index]) p8_length_hit[path.target][length_index] = 1'b1;
      end
    end

    foreach (P8_REQUIRED_LENGTHS[length_index]) begin
      string hit = p8_length_hit[path.target][length_index] ? "hit" : "MISSING";

      hit_text = {hit_text, $sformatf(" %0d=%s", P8_REQUIRED_LENGTHS[length_index], hit)};
    end
    `uvm_info("USB_FILTER_BURST_SUMMARY", $sformatf("[%s] %s: pairs=%0d/%0d writes=%0d reads=%0d checked_words=%0d beats:%s; required:%s; max 256-beat write/read=%0t/%0t", phase_name, usb_target_name(path.target), p8_pairs[path.target], P8_PAIRS_PER_PATH, p8_burst_writes[path.target], p8_burst_reads[path.target], p8_checked_words[path.target], length_text, hit_text, p8_max_256_write[path.target], p8_max_256_read[path.target]), UVM_LOW)
  endtask

  // Run P8 on both SRAM paths in order, then log the phase totals and elapsed time.
  protected task run_accepted_burst_phase();
    time start_time = $time;
    int unsigned total_pairs;
    int unsigned total_words;

    foreach (paths[index]) begin
      if (!paths[index].is_csr) begin
        run_accepted_burst_path(paths[index]);
        total_pairs += p8_pairs[paths[index].target];
        total_words += p8_checked_words[paths[index].target];
      end
    end
    `uvm_info("USB_FILTER_BURST_SUMMARY", $sformatf("[%s] Complete: %0d accepted write/read pairs, %0d words checked, elapsed %0t", phase_name, total_pairs, total_words, $time - start_time), UVM_LOW)
  endtask

  // ---------------------------------------------------------------------------
  // Completion
  // ---------------------------------------------------------------------------

  // Fatal unless every path's four P7 buckets each hold exactly
  // BURSTS_PER_BUCKET bursts and include both boundary lengths.
  protected function void verify_burst_buckets();
    foreach (paths[path_index]) begin
      for (int bucket_index = 0; bucket_index < BURST_BUCKET_COUNT; bucket_index++) begin
        burst_bucket_e bucket = burst_bucket_e'(bucket_index);

        if (burst_counts[path_index][bucket] != BURSTS_PER_BUCKET || !bucket_bounds_hit(path_index, bucket)) begin
          `uvm_fatal("USB_FILTER_COUNTS", $sformatf("%s %s bursts=%0d beats=%0d..%0d, expected %0d bursts covering %0d..%0d", usb_target_name(paths[path_index].target), bucket.name(), burst_counts[path_index][bucket], burst_min_beats[path_index][bucket], burst_max_beats[path_index][bucket], BURSTS_PER_BUCKET, BURST_MIN_BEATS, bucket_max_beats(paths[path_index], bucket)))
        end
      end
    end
    `uvm_info("USB_FILTER_SEQ", $sformatf("[%s] All %0d rejected-burst buckets hold %0d bursts with both boundary lengths", phase_name, FILTER_PATH_COUNT * BURST_BUCKET_COUNT, BURSTS_PER_BUCKET), UVM_LOW)
  endfunction

  // Fatal unless each SRAM path completed exactly P8_PAIRS_PER_PATH checked
  // pairs (one write and one read each) covering every required length, with
  // the checked-word total matching the pair lengths. Other targets must have
  // no P8 traffic.
  protected function void verify_accepted_bursts();
    for (int target_index = 0; target_index < USB_TARGET_COUNT; target_index++) begin
      usb_target_e target = usb_target_e'(target_index);
      bit is_sram = target inside {USB_DEV0_SRAM, USB_DEV1_SRAM};
      int unsigned exp_count = is_sram ? P8_PAIRS_PER_PATH : 0;

      if (p8_pairs[target] != exp_count || p8_burst_writes[target] != exp_count || p8_burst_reads[target] != exp_count ||
          p8_checked_words[target] != p8_pair_beats[target] || (is_sram && !p8_lengths_hit(target))) begin
        `uvm_fatal("USB_FILTER_COUNTS", $sformatf("%s P8 pairs=%0d writes=%0d reads=%0d checked_words=%0d pair_beats=%0d lengths_hit=%0b, expected %0d each with all required lengths", usb_target_name(target), p8_pairs[target], p8_burst_writes[target], p8_burst_reads[target], p8_checked_words[target], p8_pair_beats[target], p8_lengths_hit(target), exp_count))
      end
    end
    `uvm_info("USB_FILTER_SEQ", $sformatf("[%s] Both SRAM paths completed %0d accepted INCR write/read pairs covering every required length", phase_name, P8_PAIRS_PER_PATH), UVM_LOW)
  endfunction

  // Require the exact per-target totals implied by P0-P9, so a skipped or
  // truncated phase cannot pass. P7 adds its chosen allowed reads and writes
  // plus BURST_BUCKET_COUNT/2 * BURSTS_PER_BUCKET denials per direction. P8
  // adds exactly P8_PAIRS_PER_PATH writes, reads, and comparisons per SRAM.
  // HUB must see no traffic. Logs each total.
  protected function void verify_completion_totals();
    int unsigned exp_writes;
    int unsigned exp_reads;
    int unsigned exp_comparisons;
    int unsigned exp_denied;

    for (int target_index = 0; target_index < USB_TARGET_COUNT; target_index++) begin
      usb_target_e target = usb_target_e'(target_index);

      case (target)
        USB_DEV0_CSR, USB_DEV1_CSR:   begin exp_writes = 5; exp_reads = 9; exp_comparisons = 8; exp_denied = 3; end
        USB_DEV0_SRAM, USB_DEV1_SRAM: begin exp_writes = 4; exp_reads = 7; exp_comparisons = 7; exp_denied = 2; end
        default:                      begin exp_writes = 0; exp_reads = 0; exp_comparisons = 0; exp_denied = 0; end
      endcase
      if (target != USB_HUB) begin
        exp_writes += p7_allowed_writes[target];
        exp_reads += p7_allowed_reads[target];
        exp_comparisons += p7_allowed_reads[target];
        exp_denied += (BURST_BUCKET_COUNT / 2) * BURSTS_PER_BUCKET;
      end
      if (target inside {USB_DEV0_SRAM, USB_DEV1_SRAM}) begin
        exp_writes += P8_PAIRS_PER_PATH;
        exp_reads += P8_PAIRS_PER_PATH;
        exp_comparisons += P8_PAIRS_PER_PATH;
      end
      if (target_stats[target].writes != exp_writes || target_stats[target].reads != exp_reads ||
          target_stats[target].comparisons != exp_comparisons || denied_writes[target] != exp_denied || denied_reads[target] != exp_denied) begin
        `uvm_fatal("USB_FILTER_COUNTS", $sformatf("%s totals mismatch: accepted w/r/c=%0d/%0d/%0d denied w/r=%0d/%0d, expected %0d/%0d/%0d and %0d/%0d", usb_target_name(target), target_stats[target].writes, target_stats[target].reads, target_stats[target].comparisons, denied_writes[target], denied_reads[target], exp_writes, exp_reads, exp_comparisons, exp_denied, exp_denied))
      end
      `uvm_info("USB_FILTER_TARGET_DONE", $sformatf("%s ok w/r/c=%0d/%0d/%0d denied w/r=%0d/%0d", usb_target_name(target), target_stats[target].writes, target_stats[target].reads, target_stats[target].comparisons, denied_writes[target], denied_reads[target]), UVM_LOW)
    end
  endfunction

  // Run P0-P10 in order. Every failed check is fatal, so completed is set only
  // after every phase and the final totals pass.
  task body();
    logic [31:0] saved_route[FILTER_PATH_COUNT];

    completed = 1'b0;
    initialize_target_stats();
    foreach (shadow[target_index]) begin
      shadow[target_index] = 'x;
      denied_writes[target_index] = 0;
      denied_reads[target_index] = 0;
      p7_allowed_reads[target_index] = 0;
      p7_allowed_writes[target_index] = 0;
      p8_burst_writes[target_index] = 0;
      p8_burst_reads[target_index] = 0;
      p8_pairs[target_index] = 0;
      p8_checked_words[target_index] = 0;
      p8_pair_beats[target_index] = 0;
      p8_max_256_write[target_index] = 0;
      p8_max_256_read[target_index] = 0;
      for (int length_index = 0; length_index < P8_REQUIRED_LENGTH_COUNT; length_index++) p8_length_hit[target_index][length_index] = 1'b0;
    end
    `uvm_info("USB_FILTER_SEQ", $sformatf("Starting four-path AXI USER filter evaluation: Combo list=%0d DEV1 list=%0d USER width=%0d", USB_COMBO_NUM_PRIV_AXI_USERS, USB_DEV1_NUM_PRIV_AXI_USERS, USB_TB_AXI_USER_WIDTH), UVM_LOW)

    start_phase("P0", "program and validate random allowlists, save route words", 1'b0, 1'b0);
    program_allowlists();
    check_user_choices();
    foreach (paths[index]) begin
      if (paths[index].is_csr) begin
        read32(paths[index].target, paths[index].offset, saved_route[index], usb_axi_user_override::with_value(nonmember_user));
      end
    end

    start_phase("P1", "both policies bypassed; nonmember USER is accepted", 1'b0, 1'b0);
    foreach (paths[index]) expect_accept(paths[index], nonmember_user);

    start_phase("P2", "both policies enabled; each path accepts its own allowlisted USER", 1'b1, 1'b1);
    foreach (paths[index]) expect_accept(paths[index], path_user(paths[index], OWN_LIST));

    start_phase("P3", "opposite-device USER is denied; write does not land; read returns zero", 1'b1, 1'b1);
    foreach (paths[index]) expect_deny(paths[index], path_user(paths[index], OTHER_LIST));

    // Each P4 write uses the same value P3 blocked on that path.
    start_phase("P4", "allowed traffic succeeds after denials with filtering still enabled", 1'b1, 1'b1);
    foreach (paths[index]) expect_accept(paths[index], path_user(paths[index], OWN_LIST));

    start_phase("P5", "member USER with MSB flipped is denied on both CSR paths", 1'b1, 1'b1);
    foreach (paths[index]) begin
      if (paths[index].is_csr) expect_deny(paths[index], path_user(paths[index], OWN_LIST) ^ USER_MSB);
    end

    // P6a enables only DEV1, P6b only Combo. Paths under the bypassed policy
    // accept a nonmember USER; paths under the enabled policy reject it.
    for (int enable_combo = 0; enable_combo <= 1; enable_combo++) begin
      start_phase(enable_combo ? "P6b" : "P6a", "one policy enabled; nonmember USER", bit'(enable_combo), !bit'(enable_combo));
      foreach (paths[index]) begin
        if (paths[index].combo_policy == bit'(enable_combo)) expect_deny(paths[index], nonmember_user);
        else expect_accept(paths[index], nonmember_user);
      end
    end

    start_phase("P7", "nonmember FIXED/INCR bursts are rejected; mixed 2:1:1 with allowed single-beat reads and writes", 1'b1, 1'b1);
    run_burst_phase();

    start_phase("P8", "own-USER INCR burst writes with checked burst readback on both SRAM paths", 1'b1, 1'b1);
    run_accepted_burst_phase();

    start_phase("P9", "restore route words; final readback on every path", 1'b0, 1'b0);
    foreach (paths[index]) begin
      if (paths[index].is_csr) begin
        write32(paths[index].target, paths[index].offset, saved_route[index], usb_axi_user_override::with_value(nonmember_user));
        shadow[paths[index].target] = saved_route[index];
      end
      expect_stored(paths[index], nonmember_user);
    end

    phase_name = "P10";
    verify_burst_buckets();
    verify_accepted_bursts();
    verify_completion_totals();
    completed = 1'b1;
    `uvm_info("USB_FILTER_SEQ", "All four filter paths passed bypass, allow, deny, recovery, exact-match, independent-enable, rejected-burst, accepted-burst, and restore checks", UVM_LOW)
  endtask
endclass
