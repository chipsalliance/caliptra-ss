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
// Randomized AXI outstanding-transaction stress on all four USB wrapper ports.
// This is an AXI test, not a USB test: no enumeration or USB sequence runs,
// and device enable/connect and HUB controls are never written.
//
// Each port runs an independent worker that keeps up to max_live request
// chains in flight, launching a new chain 0..max_launch_gap AXI clocks after
// the previous one without waiting for completions. A chain is one primary
// request plus, for writes, a dependent readback. Each request is its own
// child sequence, so reads and writes overlap on every port and all four
// ports run concurrently. The environment's AXI delay policy randomizes
// VALID gaps and RREADY/BREADY stalls.
//
// Address allowlist:
//   COMBO / DEV1 CSR: interrupt enable (0x24) and interrupt route (0x2c) are
//     read/write; capability (0x30) is read-only and static. INCR reads cover
//     only 0x2c..0x30. COMBO also sends accepted-USER traffic into both
//     decoder holes, which must return SLVERR: 0x040..0x7ff (between DEV0 CSR
//     and recovery) and 0x1400..0x1fff (above the HUB aperture, below the
//     13-bit COMBO local-address wrap).
//   DEV0 / DEV1 SRAM: every word of the implemented 64 KiB, single, FIXED
//     (<= 16 beats), and INCR (<= 256 beats, never crossing 4 KiB).
// USER filtering is enabled on both policies for the whole stress phase.
// Denied requests use a nonmember or the other policy's USER.
//
// Sequence-local response/data checking and Avery-reported bus concurrency:
//   * Every write response and every read beat response is checked.
//   * A sequence-local expected-data array models every CSR allowlist word
//     and every SRAM word. SRAMs are filled with random data first.
//   * Chains that touch mutable words reserve them exclusively, so accepted
//     writes are read back and denied writes are followed by an accepted
//     preservation read before another chain can use those words.
//   * Accepted reads compare every beat; denied reads require zero data.
//   * Both SRAMs are fully swept and CSRs rechecked after the stress phase.
//   * Every launched request must complete, every scheduled and mandatory
//     operation must finish, and each port must have had multiple accepted
//     reads, multiple accepted writes, and accepted reads with writes
//     outstanding concurrently. All four ports must overlap on the bus.
// Launch counts include requests queued in Avery; concurrency counts only
// AR/AW handshakes through RLAST/B handshakes. FIXED writes are checked
// through their final beat only.

// One passive counter per Avery manager, registered only during stress.
// The address-done callbacks report acceptance, not scheduling or VALID assertion.
class usb_axi_stress_callbacks extends aaxi_callbacks;
  `uvm_object_utils(usb_axi_stress_callbacks)

  int unsigned reads;
  int unsigned writes;
  int unsigned requests_accepted;

  function new(string name = "usb_axi_stress_callbacks");
    super.new(name);
  endfunction

  virtual task master_read_addr_done(aaxi_device_class bfm, ref aaxi_master_tr tn);
    reads++;
    requests_accepted++;
  endtask

  virtual task master_write_addr_done(aaxi_device_class bfm, ref aaxi_master_tr tn);
    writes++;
    requests_accepted++;
  endtask

  virtual task read_done(aaxi_device_class bfm, ref aaxi_master_tr tn);
    if (reads == 0) begin
      `uvm_fatal("USB_STRESS_ACCOUNTING", $sformatf("%s completed a read without an accepted AR", get_name()))
    end
    reads--;
  endtask

  virtual task write_done(aaxi_device_class bfm, ref aaxi_master_tr tn);
    if (writes == 0) begin
      `uvm_fatal("USB_STRESS_ACCOUNTING", $sformatf("%s completed a write without an accepted AW", get_name()))
    end
    writes--;
  endtask
endclass

class usb_axi_stress_seq extends usb_base_seq;
  `uvm_object_utils(usb_axi_stress_seq)

  typedef bit [USB_TB_AXI_USER_WIDTH-1:0] axi_user_t;

  typedef enum int unsigned {
    PORT_COMBO,
    PORT_DEV0_SRAM,
    PORT_DEV1_CSR,
    PORT_DEV1_SRAM
  } stress_port_e;
  localparam int unsigned PORT_COUNT = 4;

  typedef enum int unsigned {
    OP_FILL,         // accepted write without readback (SRAM initialization)
    OP_WRITE,        // accepted write, then accepted readback of its footprint
    OP_READ,         // accepted read compared against the model
    OP_DENIED_WRITE, // USER-denied write (SLVERR), then accepted preservation read
    OP_DENIED_READ,  // USER-denied read (SLVERR and zero data on every beat)
    OP_HOLE_WRITE,   // COMBO decode-hole write (SLVERR)
    OP_HOLE_READ     // COMBO decode-hole read (SLVERR on every beat)
  } op_kind_e;
  localparam int unsigned OP_KIND_COUNT = 7;

  typedef enum int unsigned {
    CHECK_MODEL,
    CHECK_ZERO,
    CHECK_RESPONSE_ONLY
  } read_check_e;

  // One scheduled chain. Single-beat accesses are INCR with one beat.
  // preset_offset chains (fill and sweep) use offset; others pick at launch.
  // hole selects a decode hole for hole kinds; -1 picks one at random.
  typedef struct {
    op_kind_e kind;
    bit is_fixed;
    int unsigned beats;
    bit preset_offset;
    logic [31:0] offset;
    bit primary;
    bit mandatory;
    int hole;
  } stress_op_t;

  localparam int unsigned DEFAULT_PRIMARY_REQUESTS = 256;
  localparam int unsigned DEFAULT_MAX_LIVE = 8;
  localparam int unsigned DEFAULT_MAX_LAUNCH_GAP = 8;
  // Covers queueing behind other ports' requests and several 256-beat bursts.
  localparam time REQUEST_TIMEOUT = 200us;
  localparam int unsigned PICK_ATTEMPTS = 16;
  localparam int unsigned FIXED_MAX_BEATS = 16;
  localparam int unsigned INCR_MAX_BEATS = 256;
  localparam int unsigned WORDS_PER_4KB = 1024;
  localparam int unsigned CSR_WORD_COUNT = 16;
  localparam int unsigned CSR_ENABLE_WORD = 9;      // 0x24 interrupt enable
  localparam int unsigned CSR_ROUTE_WORD = 11;      // 0x2c interrupt route
  localparam int unsigned CSR_CAPABILITY_WORD = 12; // 0x30 static capability
  localparam int unsigned CSR_INCR_READ_BEATS = 2;  // 0x2c..0x30
  localparam logic [31:0] DEVICE_CONTROL_ADDR = 32'h00;
  // Device enable (bit 7) and connect (bit 16) must stay clear.
  localparam logic [31:0] DEVICE_ACTIVE_MASK = 32'h0001_0080;
  localparam logic [31:0] HUB_CONTROL_ADDR = HUB_BASE_ADDR + 32'h3c;
  localparam logic [31:0] HUB_ACTIVE_MASK = 32'h0001_0001;
  // COMBO local offsets the AHB decoder maps to no endpoint, so it returns
  // ERROR (usb_compound_ahb_decoder). Hole 0 lies between DEV0 CSR and
  // recovery. Hole 1 lies between the end of the HUB aperture (FIFO words
  // rounded up to a power of two) and the 13-bit local-address wrap; offsets
  // at or above the wrap alias back to DEV0 CSR, so they are not holes.
  localparam int unsigned HOLE_COUNT = 2;
  localparam logic [31:0] HUB_APERTURE_BYTES = 32'(1) << ($clog2(USB_HUB_FIFO_SIZE) + 2);
  localparam logic [31:0] HOLE_BASE[HOLE_COUNT] = '{32'h0000_0040, HUB_BASE_ADDR + HUB_APERTURE_BYTES};
  localparam logic [31:0] HOLE_LIMIT[HOLE_COUNT] = '{32'h0000_0800, 32'(1) << USB_COMBO_LOCAL_ADDR_WIDTH};

  // Tests may lower these before starting the sequence; body() validates them.
  int unsigned primary_requests = DEFAULT_PRIMARY_REQUESTS;
  int unsigned max_live = DEFAULT_MAX_LIVE;
  int unsigned max_launch_gap = DEFAULT_MAX_LAUNCH_GAP;
  bit completed;

  protected virtual usb_tb_ctrl_if #(
    .UW(usb_tb_pkg::USB_TB_AXI_USER_WIDTH),
    .COMBO_NUM_USERS(usb_tb_pkg::USB_COMBO_NUM_PRIV_AXI_USERS),
    .DEV1_NUM_USERS(usb_tb_pkg::USB_DEV1_NUM_PRIV_AXI_USERS)
  ) ctrl_vif;
  protected axi_user_t combo_users[USB_COMBO_NUM_PRIV_AXI_USERS];
  protected axi_user_t dev1_users[USB_DEV1_NUM_PRIV_AXI_USERS];
  protected axi_user_t nonmember_user;

  // Expected data and exclusive reservations, indexed by port-local word.
  protected logic [31:0] model[PORT_COUNT][];
  protected bit reserved[PORT_COUNT][];
  protected logic [31:0] saved_csr[PORT_COUNT][CSR_WORD_COUNT];

  // Scheduling and accounting.
  protected int unsigned live_chains[PORT_COUNT];
  protected int unsigned release_count[PORT_COUNT];
  protected int unsigned requests_launched[PORT_COUNT];
  protected int unsigned requests_completed[PORT_COUNT];
  protected int unsigned inflight_reads[PORT_COUNT];
  protected int unsigned inflight_writes[PORT_COUNT];
  protected int unsigned bus_reads[PORT_COUNT];
  protected int unsigned bus_writes[PORT_COUNT];
  protected int unsigned bus_requests_accepted[PORT_COUNT];
  protected usb_axi_stress_callbacks bus_trackers[PORT_COUNT];
  protected int unsigned max_inflight_reads[PORT_COUNT];
  protected int unsigned max_inflight_writes[PORT_COUNT];
  protected int unsigned max_inflight_total[PORT_COUNT];
  protected int unsigned max_live_chains[PORT_COUNT];
  protected bit read_write_overlap[PORT_COUNT];
  protected int unsigned max_active_ports;
  protected bit tracking_concurrency;
  protected int unsigned primary_completed[PORT_COUNT];
  protected int unsigned mandatory_scheduled[PORT_COUNT];
  protected int unsigned mandatory_completed[PORT_COUNT];
  protected int unsigned kind_completed[PORT_COUNT][OP_KIND_COUNT];
  protected int unsigned beats_checked[PORT_COUNT];
  // Completed decode-hole chains per hole: index 0 writes, 1 reads.
  protected int unsigned hole_completed[HOLE_COUNT][2];
  protected int unsigned request_serial;

  // Create the sequence. Models, reservations, and counters are sized and
  // cleared in body() so a sequence object can be restarted cleanly.
  function new(string name = "usb_axi_stress_seq");
    super.new(name);
  endfunction

  // Require the filter control VIF and the known-low bypass default.
  virtual task pre_start();
    super.pre_start();
    ctrl_vif = p_sequencer.ctrl_vif;
    if (ctrl_vif == null) begin
      `uvm_fatal("USB_STRESS", "USB virtual sequencer is missing the AXI USER filter control VIF")
    end
    @(posedge ctrl_vif.clk);
    if (ctrl_vif.combo_enable_axi_user_filtering !== 1'b0 || ctrl_vif.dev1_enable_axi_user_filtering !== 1'b0) begin
      `uvm_fatal("USB_STRESS", $sformatf("Filter enables are not known-low at start: combo=%b dev1=%b", ctrl_vif.combo_enable_axi_user_filtering, ctrl_vif.dev1_enable_axi_user_filtering))
    end
  endtask

  // ---------------------------------------------------------------------------
  // Port properties
  // ---------------------------------------------------------------------------

  // Map a stress port to the functional target whose Avery manager, root RAL
  // map, and address checks drive it. COMBO traffic uses the DEV0 CSR target
  // because its allowlist registers and decode holes all sit on that manager.
  protected function usb_target_e port_target(int unsigned port);
    case (port)
      PORT_COMBO:     return USB_DEV0_CSR;
      PORT_DEV0_SRAM: return USB_DEV0_SRAM;
      PORT_DEV1_CSR:  return USB_DEV1_CSR;
      default:        return USB_DEV1_SRAM;
    endcase
  endfunction

  // Short port label for log messages and child sequence names.
  protected function string port_name(int unsigned port);
    case (port)
      PORT_COMBO:     return "COMBO";
      PORT_DEV0_SRAM: return "DEV0SRAM";
      PORT_DEV1_CSR:  return "DEV1CSR";
      default:        return "DEV1SRAM";
    endcase
  endfunction

  // SRAM ports allow any word and long INCR bursts; CSR ports are restricted
  // to the small register allowlist.
  protected function bit port_is_sram(int unsigned port);
    return port == PORT_DEV0_SRAM || port == PORT_DEV1_SRAM;
  endfunction

  // COMBO and DEV0 SRAM use the Combo policy; DEV1 ports use the DEV1 policy.
  protected function bit port_uses_combo_policy(int unsigned port);
    return port == PORT_COMBO || port == PORT_DEV0_SRAM;
  endfunction

  // Size of the port's model and reservation arrays in 32-bit words: the
  // whole implemented SRAM, or the 16-word device CSR block.
  protected function int unsigned port_word_count(int unsigned port);
    if (port_is_sram(port)) begin
      return sram_implemented_bytes(port_target(port)) / 4;
    end
    return CSR_WORD_COUNT;
  endfunction

  // Implemented bits of a modeled word; interrupt enable and route share the
  // endpoint/frame/device layout captured by the device's route mask.
  protected function logic [31:0] word_mask(int unsigned port, int unsigned word);
    if (!port_is_sram(port) && (word == CSR_ENABLE_WORD || word == CSR_ROUTE_WORD)) begin
      return port == PORT_COMBO ? USB_DEV0_ROUTE_MASK : USB_DEV1_ROUTE_MASK;
    end
    return 32'hffff_ffff;
  endfunction

  // The capability word never changes, so concurrent readers share it.
  protected function bit is_static_word(int unsigned port, int unsigned word);
    return !port_is_sram(port) && word == CSR_CAPABILITY_WORD;
  endfunction

  // Kinds whose checks depend on the stored words staying unchanged by other
  // chains: accepted writes/reads, SRAM fills, and denied writes (whose
  // preservation readback must not see another chain's write). Denied reads
  // return zero data and hole accesses touch no storage, so they need none.
  protected function bit needs_reservation(op_kind_e kind);
    return kind inside {OP_FILL, OP_WRITE, OP_READ, OP_DENIED_WRITE};
  endfunction

  // Number of distinct words a request touches: FIXED bursts repeat one
  // address, INCR bursts cover one word per beat.
  protected function int unsigned footprint_words(stress_op_t op);
    return op.is_fixed ? 1 : op.beats;
  endfunction

  // A random entry from the port's own allowlist, so the request is accepted
  // while filtering is enabled. Varying the entry exercises every match slot.
  protected function axi_user_t own_user(int unsigned port);
    if (port_uses_combo_policy(port)) begin
      return combo_users[$urandom_range(USB_COMBO_NUM_PRIV_AXI_USERS - 1)];
    end
    return dev1_users[$urandom_range(USB_DEV1_NUM_PRIV_AXI_USERS - 1)];
  endfunction

  // A USER the port's policy must deny: the nonmember, or a member of the
  // other policy's allowlist, which checks that the two policies stay isolated.
  protected function axi_user_t denied_user(int unsigned port);
    axi_user_t user;

    user = nonmember_user;
    if ($urandom_range(1) == 1) begin
      if (port_uses_combo_policy(port)) begin
        user = dev1_users[$urandom_range(USB_DEV1_NUM_PRIV_AXI_USERS - 1)];
      end else begin
        user = combo_users[$urandom_range(USB_COMBO_NUM_PRIV_AXI_USERS - 1)];
      end
    end
    return user;
  endfunction

  // One-line chain description used as the prefix of every log and failure
  // message, so a failure identifies port, kind, shape, and offset.
  protected function string describe(int unsigned port, stress_op_t op, logic [31:0] offset);
    return $sformatf("%s %s %s beats=%0d offset=0x%08h", port_name(port), op.kind.name(), op.is_fixed ? "FIXED" : "INCR", op.beats, offset);
  endfunction

  // ---------------------------------------------------------------------------
  // Schedules
  // ---------------------------------------------------------------------------

  // Build a schedule entry whose offset is chosen at launch time. primary
  // marks stress-phase chains counted against primary_requests; mandatory
  // marks the seed-independent coverage chains that must all complete.
  protected function stress_op_t make_op(op_kind_e kind, bit is_fixed, int unsigned beats, bit primary = 1'b1, bit mandatory = 1'b0);
    stress_op_t op;

    op.kind = kind;
    op.is_fixed = is_fixed;
    op.beats = beats;
    op.preset_offset = 1'b0;
    op.offset = '0;
    op.primary = primary;
    op.mandatory = mandatory;
    op.hole = -1;
    return op;
  endfunction

  // Mostly short bursts, with a tail of long INCR bursts.
  protected function int unsigned random_incr_beats();
    int unsigned beats;

    randcase
      70: beats = $urandom_range(16, 2);
      20: beats = $urandom_range(64, 17);
      10: beats = $urandom_range(INCR_MAX_BEATS, 65);
    endcase
    return beats;
  endfunction

  // Choose a legal shape for the port and kind. CSR writes stay on one
  // allowlisted word (single or FIXED) so they never touch device-control
  // registers; CSR INCR reads cover only 0x2c..0x30. Shape codes:
  //   0 single beat, 1 FIXED 2..16, 2 SRAM INCR 2..256,
  //   3 decode-hole INCR 2..16 (stays in the hole), 4 CSR 2-beat INCR read.
  protected function void random_shape(int unsigned port, op_kind_e kind, output bit is_fixed, output int unsigned beats);
    int unsigned shape;

    is_fixed = 1'b0;
    beats = 1;
    if (port_is_sram(port)) begin
      randcase
        30: shape = 0;
        20: shape = 1;
        50: shape = 2;
      endcase
    end else if (kind inside {OP_HOLE_WRITE, OP_HOLE_READ}) begin
      randcase
        30: shape = 0;
        30: shape = 1;
        40: shape = 3;
      endcase
    end else if (kind inside {OP_WRITE, OP_DENIED_WRITE}) begin
      randcase
        40: shape = 0;
        60: shape = 1;
      endcase
    end else begin
      randcase
        35: shape = 0;
        45: shape = 1;
        20: shape = 4;
      endcase
    end
    case (shape)
      1: begin
        is_fixed = 1'b1;
        beats = $urandom_range(FIXED_MAX_BEATS, 2);
      end
      2: beats = random_incr_beats();
      3: beats = $urandom_range(FIXED_MAX_BEATS, 2);
      4: beats = CSR_INCR_READ_BEATS;
      default: beats = 1;
    endcase
  endfunction

  // Draw one random stress-phase chain. SRAM ports mix accepted and denied
  // reads/writes; COMBO also sends decode-hole traffic; DEV1 CSR has no hole
  // because its address is truncated to the CSR block rather than decoded.
  protected function stress_op_t random_op(int unsigned port);
    op_kind_e kind;
    bit is_fixed;
    int unsigned beats;

    if (port_is_sram(port)) begin
      randcase
        35: kind = OP_WRITE;
        30: kind = OP_READ;
        15: kind = OP_DENIED_WRITE;
        20: kind = OP_DENIED_READ;
      endcase
    end else if (port == PORT_COMBO) begin
      randcase
        25: kind = OP_WRITE;
        30: kind = OP_READ;
        10: kind = OP_DENIED_WRITE;
        15: kind = OP_DENIED_READ;
        10: kind = OP_HOLE_WRITE;
        10: kind = OP_HOLE_READ;
      endcase
    end else begin
      randcase
        30: kind = OP_WRITE;
        35: kind = OP_READ;
        15: kind = OP_DENIED_WRITE;
        20: kind = OP_DENIED_READ;
      endcase
    end
    random_shape(port, kind, is_fixed, beats);
    return make_op(kind, is_fixed, beats);
  endfunction

  // Required shapes per port, guaranteeing minimum/maximum lengths and every
  // accepted, denied, and decode-hole class regardless of seed.
  protected function void add_mandatory_ops(int unsigned port, ref stress_op_t ops[$]);
    op_kind_e kinds[$];

    if (port_is_sram(port)) begin
      kinds = {OP_WRITE, OP_READ, OP_DENIED_WRITE, OP_DENIED_READ};
      foreach (kinds[index]) begin
        ops.push_back(make_op(kinds[index], 1'b0, 1, 1'b1, 1'b1));
        ops.push_back(make_op(kinds[index], 1'b1, 2, 1'b1, 1'b1));
        ops.push_back(make_op(kinds[index], 1'b1, FIXED_MAX_BEATS, 1'b1, 1'b1));
        ops.push_back(make_op(kinds[index], 1'b0, 2, 1'b1, 1'b1));
        ops.push_back(make_op(kinds[index], 1'b0, 16, 1'b1, 1'b1));
        ops.push_back(make_op(kinds[index], 1'b0, 17, 1'b1, 1'b1));
        ops.push_back(make_op(kinds[index], 1'b0, INCR_MAX_BEATS, 1'b1, 1'b1));
      end
      return;
    end
    kinds = {OP_WRITE, OP_DENIED_WRITE};
    foreach (kinds[index]) begin
      ops.push_back(make_op(kinds[index], 1'b0, 1, 1'b1, 1'b1));
      ops.push_back(make_op(kinds[index], 1'b1, 2, 1'b1, 1'b1));
      ops.push_back(make_op(kinds[index], 1'b1, FIXED_MAX_BEATS, 1'b1, 1'b1));
    end
    kinds = {OP_READ, OP_DENIED_READ};
    foreach (kinds[index]) begin
      ops.push_back(make_op(kinds[index], 1'b0, 1, 1'b1, 1'b1));
      ops.push_back(make_op(kinds[index], 1'b1, FIXED_MAX_BEATS, 1'b1, 1'b1));
      ops.push_back(make_op(kinds[index], 1'b0, CSR_INCR_READ_BEATS, 1'b1, 1'b1));
    end
    if (port == PORT_COMBO) begin
      kinds = {OP_HOLE_WRITE, OP_HOLE_READ};
      for (int hole = 0; hole < HOLE_COUNT; hole++) begin
        foreach (kinds[index]) begin
          add_hole_op(ops, make_op(kinds[index], 1'b0, 1, 1'b1, 1'b1), hole);
          add_hole_op(ops, make_op(kinds[index], 1'b1, FIXED_MAX_BEATS, 1'b1, 1'b1), hole);
          add_hole_op(ops, make_op(kinds[index], 1'b0, FIXED_MAX_BEATS, 1'b1, 1'b1), hole);
        end
      end
    end
  endfunction

  // Queue a mandatory decode-hole op pinned to one hole, so every seed sends
  // single, FIXED, and INCR reads and writes into each hole.
  protected function void add_hole_op(ref stress_op_t ops[$], input stress_op_t op, input int hole);
    op.hole = hole;
    ops.push_back(op);
  endfunction

  // Mandatory operations plus random fill, shuffled so required shapes mix
  // with random traffic instead of running as a directed prefix.
  protected function void build_stress_schedule(int unsigned port, ref stress_op_t ops[$]);
    ops.delete();
    add_mandatory_ops(port, ops);
    mandatory_scheduled[port] = ops.size();
    if (ops.size() > primary_requests) begin
      `uvm_fatal("USB_STRESS", $sformatf("%s needs %0d mandatory operations but primary_requests=%0d", port_name(port), ops.size(), primary_requests))
    end
    while (ops.size() < primary_requests) begin
      ops.push_back(random_op(port));
    end
    ops.shuffle();
  endfunction

  // Whole-SRAM 256-beat INCR bursts at 1 KiB-aligned offsets, so none crosses
  // a 4 KiB boundary. kind is OP_FILL for initialization or OP_READ to sweep.
  protected function void build_sram_pass(int unsigned port, op_kind_e kind, ref stress_op_t ops[$]);
    stress_op_t op;

    ops.delete();
    for (int unsigned word = 0; word < port_word_count(port); word += INCR_MAX_BEATS) begin
      op = make_op(kind, 1'b0, INCR_MAX_BEATS, 1'b0, 1'b0);
      op.preset_offset = 1'b1;
      op.offset = 32'(word * 4);
      ops.push_back(op);
    end
  endfunction

  // ---------------------------------------------------------------------------
  // Address selection and reservation
  // ---------------------------------------------------------------------------

  // Reserve every mutable word in the footprint, or nothing if any is taken.
  protected function bit reserve(int unsigned port, logic [31:0] offset, int unsigned words);
    int unsigned first_word;

    first_word = offset >> 2;
    for (int unsigned word = first_word; word < first_word + words; word++) begin
      if (!is_static_word(port, word) && reserved[port][word]) begin
        return 1'b0;
      end
    end
    for (int unsigned word = first_word; word < first_word + words; word++) begin
      if (!is_static_word(port, word)) begin
        reserved[port][word] = 1'b1;
      end
    end
    return 1'b1;
  endfunction

  // Free the footprint reserved by acquire() once a chain's final check has
  // passed. The caller then bumps release_count to wake blocked acquirers.
  protected function void release_words(int unsigned port, stress_op_t op, logic [31:0] offset);
    int unsigned first_word;

    if (!needs_reservation(op.kind)) begin
      return;
    end
    first_word = offset >> 2;
    for (int unsigned word = first_word; word < first_word + footprint_words(op); word++) begin
      if (!is_static_word(port, word)) begin
        reserved[port][word] = 1'b0;
      end
    end
  endfunction

  // Pick one candidate offset for op and try to reserve its footprint. SRAM
  // INCR footprints are pulled back to stay inside their 4 KiB page.
  protected function bit try_pick(int unsigned port, stress_op_t op, output logic [31:0] offset);
    int unsigned words;
    int unsigned first_word;
    int unsigned last_start;
    int hole;

    words = footprint_words(op);
    if (op.preset_offset) begin
      first_word = op.offset >> 2;
    end else if (op.kind inside {OP_HOLE_WRITE, OP_HOLE_READ}) begin
      hole = op.hole >= 0 ? op.hole : $urandom_range(HOLE_COUNT - 1);
      last_start = (HOLE_LIMIT[hole] >> 2) - words;
      first_word = $urandom_range(last_start, HOLE_BASE[hole] >> 2);
    end else if (port_is_sram(port)) begin
      first_word = $urandom_range(port_word_count(port) - words);
      if ((first_word % WORDS_PER_4KB) + words > WORDS_PER_4KB) begin
        first_word = (first_word / WORDS_PER_4KB) * WORDS_PER_4KB + WORDS_PER_4KB - words;
      end
    end else if (!op.is_fixed && op.beats > 1) begin
      first_word = CSR_ROUTE_WORD;
    end else if (op.kind inside {OP_WRITE, OP_DENIED_WRITE}) begin
      first_word = $urandom_range(1) ? CSR_ROUTE_WORD : CSR_ENABLE_WORD;
    end else begin
      randcase
        1: first_word = CSR_ENABLE_WORD;
        1: first_word = CSR_ROUTE_WORD;
        1: first_word = CSR_CAPABILITY_WORD;
      endcase
    end
    offset = 32'(first_word * 4);
    if (!needs_reservation(op.kind)) begin
      return 1'b1;
    end
    return reserve(port, offset, words);
  endfunction

  // Index of the decode hole wholly containing [offset, last_offset], or -1.
  protected function int hole_index(logic [31:0] offset, logic [31:0] last_offset);
    for (int hole = 0; hole < HOLE_COUNT; hole++) begin
      if (offset >= HOLE_BASE[hole] && last_offset < HOLE_LIMIT[hole]) begin
        return hole;
      end
    end
    return -1;
  endfunction

  // Check that a chosen footprint is legal before any request is built.
  protected function void check_footprint(int unsigned port, stress_op_t op, logic [31:0] offset);
    int unsigned words;
    logic [31:0] last_offset;

    words = footprint_words(op);
    last_offset = offset + 32'(4 * (words - 1));
    if (op.kind inside {OP_HOLE_WRITE, OP_HOLE_READ}) begin
      if (port != PORT_COMBO || hole_index(offset, last_offset) < 0) begin
        `uvm_fatal("USB_STRESS", $sformatf("Illegal decode-hole footprint: %s", describe(port, op, offset)))
      end
    end else begin
      check_address(port_target(port), offset);
      check_address(port_target(port), last_offset);
    end
    if ((offset[11:0] + 13'(4 * words)) > 13'h1000) begin
      `uvm_fatal("USB_STRESS", $sformatf("Burst crosses a 4 KiB boundary: %s", describe(port, op, offset)))
    end
    if ((op.is_fixed && op.beats > FIXED_MAX_BEATS) || op.beats > INCR_MAX_BEATS || op.beats == 0) begin
      `uvm_fatal("USB_STRESS", $sformatf("Illegal burst length: %s", describe(port, op, offset)))
    end
  endfunction

  // Block until op has an offset and, if needed, its reserved footprint.
  // Retries wait for another chain on the same port to release words.
  protected task acquire(int unsigned port, stress_op_t op, output logic [31:0] offset);
    int unsigned snapshot;

    forever begin
      snapshot = release_count[port];
      for (int unsigned attempt = 0; attempt < PICK_ATTEMPTS; attempt++) begin
        if (try_pick(port, op, offset)) begin
          check_footprint(port, op, offset);
          return;
        end
      end
      if (live_chains[port] == 0) begin
        `uvm_fatal("USB_STRESS", $sformatf("No reservation possible with no live chains: %s", describe(port, op, op.offset)))
      end
      wait (release_count[port] != snapshot);
    end
  endtask

  // ---------------------------------------------------------------------------
  // Requests and checks
  // ---------------------------------------------------------------------------

  // Build a full-strobe 32-bit request of any legal FIXED/INCR shape. Hole
  // offsets are formed directly from the COMBO map base like any other offset.
  protected function aaxi_master_tr build_request(int unsigned port, logic [31:0] offset, bit is_write, bit is_fixed, int unsigned beats, axi_user_t user, logic [31:0] write_data[$]);
    aaxi_master_tr request;

    request = create_transaction(port_target(port), offset, is_write, '0, usb_axi_user_override::with_value(user));
    request.len = beats - 1;
    request.burst = is_fixed ? AAXI_BURST_FIXED : AAXI_BURST_INCR;
    request.wuser_A = new[beats];
    foreach (request.wuser_A[beat]) begin
      request.wuser_A[beat] = user;
    end
    if (is_write) begin
      if (write_data.size() != beats) begin
        `uvm_fatal("USB_STRESS", $sformatf("%s write has %0d data words for %0d beats", port_name(port), write_data.size(), beats))
      end
      request.data.delete();
      request.strobes.delete();
      foreach (write_data[beat]) begin
        for (int unsigned lane = 0; lane < USB_AXI_DATA_WIDTH / 8; lane++) begin
          request.data.push_back(write_data[beat][lane * 8 +: 8]);
          request.strobes.push_back(1'b1);
        end
      end
    end
    return request;
  endfunction

  // Sample all ports before recording overlap, so a completion on one port
  // and acceptance on another at the same edge cannot create false overlap.
  protected function void update_concurrency_marks();
    int unsigned active_ports;

    active_ports = 0;
    for (int unsigned port = 0; port < PORT_COUNT; port++) begin
      if (bus_reads[port] > max_inflight_reads[port]) max_inflight_reads[port] = bus_reads[port];
      if (bus_writes[port] > max_inflight_writes[port]) max_inflight_writes[port] = bus_writes[port];
      if (bus_reads[port] + bus_writes[port] > max_inflight_total[port]) max_inflight_total[port] = bus_reads[port] + bus_writes[port];
      if (bus_reads[port] > 0 && bus_writes[port] > 0) read_write_overlap[port] = 1'b1;
      if (bus_reads[port] + bus_writes[port] > 0) active_ports++;
    end
    if (active_ports > max_active_ports) max_active_ports = active_ports;
  endfunction

 
  // Passively count accepted but unfinished AXI requests on all four USB ports.
  // Avery's address-done callbacks add reads/writes; its transaction-done
  // callbacks remove them. Requests still queued in the testbench do not count.
  // Sample those counters at the falling edge, after all rising-edge callbacks
  // have finished. This avoids counting same-edge replacement as overlap.
  // The peaks and overlap flags let check_accounting() verify that USB accepted
  // multiple requests before earlier ones finished, rather than one at a time.
  //
  // Reset makes tracking unreliable and is fatal here. The callbacks also
  // stop on a completion with no counted request, indicating a DUT or monitor
  // problem. Existing AXI protocol checkers still check the bus signals.
  // Insufficient overlap is checked separately by check_accounting().
  protected task monitor_bus_concurrency();
    while (tracking_concurrency) begin
      @(negedge ctrl_vif.clk);
      if (ctrl_vif.rst_n !== 1'b1) begin
        `uvm_fatal("USB_STRESS_ACCOUNTING", "Reset is not deasserted during stress monitoring")
      end
      for (int unsigned port = 0; port < PORT_COUNT; port++) begin
        bus_reads[port] = bus_trackers[port].reads;
        bus_writes[port] = bus_trackers[port].writes;
        bus_requests_accepted[port] = bus_trackers[port].requests_accepted;
      end
      update_concurrency_marks();
    end
  endtask

  // Launch one request as its own child sequence and wait for its completion.
  // Other chains keep launching meanwhile; timeout is per request.
  protected task issue(int unsigned port, aaxi_master_tr request);
    usb_axi_single_request_seq child;
    bit is_write;
    int unsigned serial;

    is_write = request.kind == AAXI_WRITE;
    serial = request_serial;
    request_serial++;
    child = usb_axi_single_request_seq::type_id::create($sformatf("%s_request%0d", port_name(port), serial));
    child.target = port_target(port);
    child.transaction = request;
    child.timeout = REQUEST_TIMEOUT;
    requests_launched[port]++;
    if (is_write) inflight_writes[port]++;
    else inflight_reads[port]++;
    child.start(p_sequencer, this);
    if (is_write) inflight_writes[port]--;
    else inflight_reads[port]--;
    requests_completed[port]++;
  endtask

  // Require the single B response to match: OKAY for accepted writes, SLVERR
  // for USER-denied and decode-hole writes.
  protected function void check_write_response(int unsigned port, aaxi_master_tr request, aaxi_resp_type expected_resp, string label);
    if (request.resp !== expected_resp) begin
      `uvm_fatal("USB_STRESS_RESPONSE", $sformatf("%s: write addr=0x%08h user=0x%08h response=0x%0h, expected 0x%0h", label, request.addr, request.awuser, request.resp, expected_resp))
    end
  endfunction

  // Require exactly one response and one data word per beat, the expected
  // response on each, and, per mode, model data or zero data on each beat.
  protected function void check_read(int unsigned port, aaxi_master_tr request, logic [31:0] offset, bit is_fixed, int unsigned beats, aaxi_resp_type expected_resp, read_check_e mode, string label);
    logic [31:0] actual;
    logic [31:0] expected;
    logic [31:0] mask;
    int unsigned word;

    if (request.rresp_Q.size() != beats || request.data.size() != beats * (USB_AXI_DATA_WIDTH / 8)) begin
      `uvm_fatal("USB_STRESS_READ_LOSS", $sformatf("%s: read addr=0x%08h returned %0d responses and %0d bytes, expected %0d beats", label, request.addr, request.rresp_Q.size(), request.data.size(), beats))
    end
    for (int unsigned beat = 0; beat < beats; beat++) begin
      for (int unsigned lane = 0; lane < USB_AXI_DATA_WIDTH / 8; lane++) begin
        actual[lane * 8 +: 8] = request.data[beat * (USB_AXI_DATA_WIDTH / 8) + lane];
      end
      if (request.rresp_Q[beat] !== expected_resp) begin
        `uvm_fatal("USB_STRESS_RESPONSE", $sformatf("%s: beat %0d/%0d addr=0x%08h user=0x%08h response=0x%0h, expected 0x%0h", label, beat + 1, beats, request.addr, request.aruser, request.rresp_Q[beat], expected_resp))
      end
      case (mode)
        CHECK_MODEL: begin
          word = (offset >> 2) + (is_fixed ? 0 : beat);
          expected = model[port][word];
          mask = word_mask(port, word);
          if ($isunknown(expected)) begin
            `uvm_fatal("USB_STRESS", $sformatf("%s: word %0d has no expected value", label, word))
          end
          if ((actual & mask) !== (expected & mask)) begin
            `uvm_fatal("USB_STRESS_DATA", $sformatf("%s: beat %0d/%0d word offset=0x%08h expected=0x%08h actual=0x%08h mask=0x%08h", label, beat + 1, beats, word * 4, expected, actual, mask))
          end
        end
        CHECK_ZERO: begin
          if (actual !== '0) begin
            `uvm_fatal("USB_STRESS_DATA", $sformatf("%s: denied beat %0d/%0d returned 0x%08h, expected zero", label, beat + 1, beats, actual))
          end
        end
        default: ;
      endcase
      beats_checked[port]++;
    end
  endfunction

  // Record an accepted write in the model: INCR beats land on consecutive
  // words; FIXED beats overwrite one word, leaving the final beat.
  protected function void apply_write(int unsigned port, logic [31:0] offset, stress_op_t op, logic [31:0] write_data[$]);
    int unsigned word;

    foreach (write_data[beat]) begin
      word = (offset >> 2) + (op.is_fixed ? 0 : beat);
      model[port][word] = write_data[beat] & word_mask(port, word);
    end
  endfunction

  // Execute one chain. Its reservation covers the dependent readback, so the
  // readback observes exactly this chain's effect (or lack of one).
  protected task run_chain(int unsigned port, stress_op_t op, logic [31:0] offset);
    logic [31:0] write_data[$];
    logic [31:0] no_data[$];
    aaxi_master_tr request;
    string label;

    label = describe(port, op, offset);
    `uvm_info("USB_STRESS_CHAIN", $sformatf("Start %s", label), UVM_HIGH)
    case (op.kind)
      OP_FILL, OP_WRITE, OP_DENIED_WRITE, OP_HOLE_WRITE: begin
        for (int unsigned beat = 0; beat < op.beats; beat++) begin
          write_data.push_back($urandom());
        end
        request = build_request(port, offset, 1'b1, op.is_fixed, op.beats, op.kind == OP_DENIED_WRITE ? denied_user(port) : own_user(port), write_data);
        issue(port, request);
        check_write_response(port, request, op.kind inside {OP_FILL, OP_WRITE} ? AAXI_RESP_OKAY : AAXI_RESP_SLVERR, label);
        if (op.kind inside {OP_FILL, OP_WRITE}) begin
          apply_write(port, offset, op, write_data);
        end
        if (op.kind inside {OP_WRITE, OP_DENIED_WRITE}) begin
          request = build_request(port, offset, 1'b0, 1'b0, footprint_words(op), own_user(port), no_data);
          issue(port, request);
          check_read(port, request, offset, 1'b0, footprint_words(op), AAXI_RESP_OKAY, CHECK_MODEL, {label, " readback"});
        end
      end
      OP_READ: begin
        request = build_request(port, offset, 1'b0, op.is_fixed, op.beats, own_user(port), no_data);
        issue(port, request);
        check_read(port, request, offset, op.is_fixed, op.beats, AAXI_RESP_OKAY, CHECK_MODEL, label);
      end
      OP_DENIED_READ: begin
        request = build_request(port, offset, 1'b0, op.is_fixed, op.beats, denied_user(port), no_data);
        issue(port, request);
        check_read(port, request, offset, op.is_fixed, op.beats, AAXI_RESP_SLVERR, CHECK_ZERO, label);
      end
      OP_HOLE_READ: begin
        request = build_request(port, offset, 1'b0, op.is_fixed, op.beats, own_user(port), no_data);
        issue(port, request);
        check_read(port, request, offset, op.is_fixed, op.beats, AAXI_RESP_SLVERR, CHECK_RESPONSE_ONLY, label);
      end
      default: `uvm_fatal("USB_STRESS", $sformatf("Unknown chain kind: %s", label))
    endcase
    kind_completed[port][op.kind]++;
    if (op.kind inside {OP_HOLE_WRITE, OP_HOLE_READ}) begin
      hole_completed[hole_index(offset, offset + 32'(4 * (footprint_words(op) - 1)))][op.kind == OP_HOLE_READ]++;
    end
    if (op.primary) primary_completed[port]++;
    if (op.mandatory) mandatory_completed[port]++;
    `uvm_info("USB_STRESS_CHAIN", $sformatf("Completed %s", label), UVM_HIGH)
  endtask

  // Keep up to max_live chains in flight on one port. Each new chain launches
  // after a random 0..max_launch_gap clock gap without waiting for earlier
  // chains; the worker returns only after all of its chains finish.
  protected task run_port(int unsigned port, stress_op_t ops[$]);
    logic [31:0] offset;

    foreach (ops[index]) begin
      wait (live_chains[port] < max_live);
      acquire(port, ops[index], offset);
      live_chains[port]++;
      if (live_chains[port] > max_live_chains[port]) max_live_chains[port] = live_chains[port];
      fork
        automatic stress_op_t chain_op = ops[index];
        automatic logic [31:0] chain_offset = offset;
        begin
          run_chain(port, chain_op, chain_offset);
          release_words(port, chain_op, chain_offset);
          live_chains[port]--;
          release_count[port]++;
        end
      join_none
      repeat ($urandom_range(max_launch_gap)) @(posedge ctrl_vif.clk);
    end
    wait fork;
  endtask

  // ---------------------------------------------------------------------------
  // Phases
  // ---------------------------------------------------------------------------

  // Reject knob values that break the test's guarantees: at least two live
  // chains are needed for overlap, and no more than the Avery managers'
  // configured outstanding depth may be issued.
  protected function void validate_settings();
    if (max_live < 2 || max_live > USB_AXI_MAX_OUTSTANDING) begin
      `uvm_fatal("USB_STRESS", $sformatf("max_live=%0d must be 2..%0d", max_live, USB_AXI_MAX_OUTSTANDING))
    end
    if (max_launch_gap > 64) begin
      `uvm_fatal("USB_STRESS", $sformatf("max_launch_gap=%0d must be 0..64 clocks", max_launch_gap))
    end
    // A HUB FIFO size that fills its power-of-two aperture up to the local
    // wrap would leave hole 1 too small for a 16-beat burst. Holes never
    // span 4 KiB pages, and check_footprint() rejects any burst that would.
    for (int hole = 0; hole < HOLE_COUNT; hole++) begin
      if (HOLE_LIMIT[hole] < HOLE_BASE[hole] + 32'(4 * FIXED_MAX_BEATS)) begin
        `uvm_fatal("USB_STRESS", $sformatf("Decode hole %0d 0x%08h..0x%08h cannot hold a %0d-beat burst", hole, HOLE_BASE[hole], HOLE_LIMIT[hole] - 1, FIXED_MAX_BEATS))
      end
    end
    `uvm_info("USB_STRESS", $sformatf("COMBO decode holes: 0x%08h..0x%08h and 0x%08h..0x%08h", HOLE_BASE[0], HOLE_LIMIT[0] - 1, HOLE_BASE[1], HOLE_LIMIT[1] - 1), UVM_LOW)
  endfunction

  // Size the per-port model and reservation arrays and clear all counters.
  // Model words start as X, so reading a word before it is written or
  // captured is reported rather than compared against a guessed value.
  protected function void initialize_state();
    request_serial = 0;
    max_active_ports = 0;
    tracking_concurrency = 1'b0;
    for (int unsigned port = 0; port < PORT_COUNT; port++) begin
      model[port] = new[port_word_count(port)];
      reserved[port] = new[port_word_count(port)];
      foreach (model[port][word]) begin
        model[port][word] = 'x;
        reserved[port][word] = 1'b0;
      end
      live_chains[port] = 0;
      release_count[port] = 0;
      requests_launched[port] = 0;
      requests_completed[port] = 0;
      inflight_reads[port] = 0;
      inflight_writes[port] = 0;
      bus_reads[port] = 0;
      bus_writes[port] = 0;
      bus_requests_accepted[port] = 0;
      max_inflight_reads[port] = 0;
      max_inflight_writes[port] = 0;
      max_inflight_total[port] = 0;
      max_live_chains[port] = 0;
      read_write_overlap[port] = 1'b0;
      primary_completed[port] = 0;
      mandatory_scheduled[port] = 0;
      mandatory_completed[port] = 0;
      beats_checked[port] = 0;
      foreach (kind_completed[port][kind]) kind_completed[port][kind] = 0;
    end
    foreach (hole_completed[hole, direction]) hole_completed[hole][direction] = 0;
  endfunction

  // Both device controllers must be disabled and disconnected and the HUB
  // disabled, so AXI traffic cannot start USB activity. Uses the caller's USER.
  protected task check_usb_idle(string when, input usb_axi_user_override combo_user = null, input usb_axi_user_override dev1_user = null);
    expect32(USB_DEV0_CSR, DEVICE_CONTROL_ADDR, '0, DEVICE_ACTIVE_MASK, combo_user);
    expect32(USB_DEV1_CSR, DEVICE_CONTROL_ADDR, '0, DEVICE_ACTIVE_MASK, dev1_user);
    expect32(USB_HUB, HUB_CONTROL_ADDR, '0, HUB_ACTIVE_MASK, combo_user);
    `uvm_info("USB_STRESS", $sformatf("%s: both devices disabled/disconnected and HUB disabled", when), UVM_LOW)
  endtask

  // Save the CSR allowlist words for restoration and seed the model. The
  // capability word is static, so its first value becomes the expected value.
  protected task capture_csr_state();
    int unsigned words[3] = '{CSR_ENABLE_WORD, CSR_ROUTE_WORD, CSR_CAPABILITY_WORD};
    int unsigned ports[2] = '{PORT_COMBO, PORT_DEV1_CSR};
    logic [31:0] data;

    foreach (ports[port_index]) begin
      foreach (words[word_index]) begin
        read32(port_target(ports[port_index]), 32'(words[word_index] * 4), data);
        saved_csr[ports[port_index]][words[word_index]] = data;
        model[ports[port_index]][words[word_index]] = data & word_mask(ports[port_index], words[word_index]);
      end
      if (data[4:0] !== 5'(ports[port_index] == PORT_COMBO ? USB_DEV0_NBPHYSEP : USB_DEV1_NBPHYSEP)) begin
        `uvm_fatal("USB_STRESS", $sformatf("%s capability 0x%08h does not report the configured endpoint count", port_name(ports[port_index]), data))
      end
      `uvm_info("USB_STRESS", $sformatf("%s CSR start: enable=0x%08h route=0x%08h capability=0x%08h", port_name(ports[port_index]), saved_csr[ports[port_index]][CSR_ENABLE_WORD], saved_csr[ports[port_index]][CSR_ROUTE_WORD], saved_csr[ports[port_index]][CSR_CAPABILITY_WORD]), UVM_LOW)
    end
  endtask

  // Randomize unique allowlists and nonmember, then enable both policies.
  // Policy signals change only at a clock edge while no request is in flight.
  protected task enable_filtering();
    if (!std::randomize(combo_users, dev1_users, nonmember_user) with {
          unique {combo_users, dev1_users, nonmember_user};
        }) begin
      `uvm_fatal("USB_STRESS", "Unable to randomize the AXI USER allowlists")
    end
    @(posedge ctrl_vif.clk);
    foreach (combo_users[index]) ctrl_vif.combo_priv_axi_users[index] <= combo_users[index];
    foreach (dev1_users[index]) ctrl_vif.dev1_priv_axi_users[index] <= dev1_users[index];
    ctrl_vif.combo_enable_axi_user_filtering <= 1'b1;
    ctrl_vif.dev1_enable_axi_user_filtering <= 1'b1;
    @(posedge ctrl_vif.clk);
    foreach (combo_users[index]) begin
      if (ctrl_vif.combo_priv_axi_users[index] !== combo_users[index]) begin
        `uvm_fatal("USB_STRESS", $sformatf("Combo allowlist entry %0d did not update", index))
      end
    end
    foreach (dev1_users[index]) begin
      if (ctrl_vif.dev1_priv_axi_users[index] !== dev1_users[index]) begin
        `uvm_fatal("USB_STRESS", $sformatf("DEV1 allowlist entry %0d did not update", index))
      end
    end
    if (ctrl_vif.combo_enable_axi_user_filtering !== 1'b1 || ctrl_vif.dev1_enable_axi_user_filtering !== 1'b1) begin
      `uvm_fatal("USB_STRESS", "Filter enables did not assert")
    end
    `uvm_info("USB_STRESS", $sformatf("Filtering enabled: Combo=%p DEV1=%p nonmember=0x%08h", combo_users, dev1_users, nonmember_user), UVM_LOW)
  endtask

  // Return both policies to bypass after all stress traffic has drained, so
  // restore_csr_state() can use ordinary random-USER accesses.
  protected task disable_filtering();
    @(posedge ctrl_vif.clk);
    ctrl_vif.combo_enable_axi_user_filtering <= 1'b0;
    ctrl_vif.dev1_enable_axi_user_filtering <= 1'b0;
    @(posedge ctrl_vif.clk);
    if (ctrl_vif.combo_enable_axi_user_filtering !== 1'b0 || ctrl_vif.dev1_enable_axi_user_filtering !== 1'b0) begin
      `uvm_fatal("USB_STRESS", "Filter enables did not deassert")
    end
  endtask

  // Fill (OP_FILL) or sweep (OP_READ) both SRAMs, each with overlapping bursts.
  protected task run_sram_pass(op_kind_e kind);
    stress_op_t dev0_ops[$];
    stress_op_t dev1_ops[$];

    build_sram_pass(PORT_DEV0_SRAM, kind, dev0_ops);
    build_sram_pass(PORT_DEV1_SRAM, kind, dev1_ops);
    `uvm_info("USB_STRESS", $sformatf("SRAM %s: %0d and %0d 256-beat INCR bursts on DEV0/DEV1 SRAM", kind == OP_FILL ? "fill" : "sweep", dev0_ops.size(), dev1_ops.size()), UVM_LOW)
    fork
      run_port(PORT_DEV0_SRAM, dev0_ops);
      run_port(PORT_DEV1_SRAM, dev1_ops);
    join
  endtask

  // All four workers run concurrently until every scheduled chain finishes.
  protected task run_stress();
    stress_op_t combo_ops[$];
    stress_op_t dev0_ops[$];
    stress_op_t dev1_csr_ops[$];
    stress_op_t dev1_ops[$];
    int unsigned requests_before_stress[PORT_COUNT];
    aaxi_agent managers[PORT_COUNT];
    aaxi_sequencer manager_sequencer;

    build_stress_schedule(PORT_COMBO, combo_ops);
    build_stress_schedule(PORT_DEV0_SRAM, dev0_ops);
    build_stress_schedule(PORT_DEV1_CSR, dev1_csr_ops);
    build_stress_schedule(PORT_DEV1_SRAM, dev1_ops);
    `uvm_info("USB_STRESS", $sformatf("Stress: %0d chains per port, up to %0d live per port, 0..%0d clock launch gaps", primary_requests, max_live, max_launch_gap), UVM_LOW)
    // Start between sampling edges after initialization traffic has drained.
    @(negedge ctrl_vif.clk);
    requests_before_stress = requests_launched;
    for (int unsigned port = 0; port < PORT_COUNT; port++) begin
      manager_sequencer = sequencer_for(port_target(port));
      managers[port] = manager_sequencer.cfg.agent;
      if (managers[port] == null) begin
        `uvm_fatal("USB_STRESS", $sformatf("%s Avery manager is missing", port_name(port)))
      end
      if (managers[port].driver == null || managers[port].bfm == null) begin
        `uvm_fatal("USB_STRESS", $sformatf("%s Avery manager BFM is missing", port_name(port)))
      end
      bus_trackers[port] = usb_axi_stress_callbacks::type_id::create({port_name(port), "_bus_tracker"});
      managers[port].add_callback(bus_trackers[port]);
    end
    tracking_concurrency = 1'b1;
    fork
      monitor_bus_concurrency();
      begin
        fork
          run_port(PORT_COMBO, combo_ops);
          run_port(PORT_DEV0_SRAM, dev0_ops);
          run_port(PORT_DEV1_CSR, dev1_csr_ops);
          run_port(PORT_DEV1_SRAM, dev1_ops);
        join
        @(negedge ctrl_vif.clk);
        tracking_concurrency = 1'b0;
      end
    join
    for (int unsigned port = 0; port < PORT_COUNT; port++) begin
      managers[port].delete_callback(bus_trackers[port]);
      if (bus_requests_accepted[port] != requests_launched[port] - requests_before_stress[port] || bus_reads[port] != 0 || bus_writes[port] != 0) begin
        `uvm_fatal("USB_STRESS_ACCOUNTING", $sformatf("%s stress bus accepted=%0d launched=%0d outstanding reads=%0d writes=%0d", port_name(port), bus_requests_accepted[port], requests_launched[port] - requests_before_stress[port], bus_reads[port], bus_writes[port]))
      end
    end
  endtask

  // Recheck every modeled CSR word through an allowed USER.
  protected task check_final_csr_state();
    int unsigned words[3] = '{CSR_ENABLE_WORD, CSR_ROUTE_WORD, CSR_CAPABILITY_WORD};
    int unsigned ports[2] = '{PORT_COMBO, PORT_DEV1_CSR};

    foreach (ports[port_index]) begin
      foreach (words[word_index]) begin
        expect32(port_target(ports[port_index]), 32'(words[word_index] * 4), model[ports[port_index]][words[word_index]], word_mask(ports[port_index], words[word_index]), usb_axi_user_override::with_value(own_user(ports[port_index])));
      end
    end
  endtask

  // With filtering bypassed, restore the writable CSR words to their start values.
  protected task restore_csr_state();
    int unsigned words[2] = '{CSR_ENABLE_WORD, CSR_ROUTE_WORD};
    int unsigned ports[2] = '{PORT_COMBO, PORT_DEV1_CSR};
    int unsigned port;
    int unsigned word;

    foreach (ports[port_index]) begin
      foreach (words[word_index]) begin
        port = ports[port_index];
        word = words[word_index];
        write32(port_target(port), 32'(word * 4), saved_csr[port][word] & word_mask(port, word));
        expect32(port_target(port), 32'(word * 4), saved_csr[port][word], word_mask(port, word));
      end
    end
  endtask

  // Final accounting: nothing left in flight, every request completed, every
  // scheduled and mandatory chain finished, and each port overlapped reads
  // and writes with more than one of each accepted and outstanding at once.
  protected function void check_accounting();
    for (int unsigned port = 0; port < PORT_COUNT; port++) begin
      if (live_chains[port] != 0 || inflight_reads[port] != 0 || inflight_writes[port] != 0) begin
        `uvm_fatal("USB_STRESS_ACCOUNTING", $sformatf("%s left chains=%0d reads=%0d writes=%0d in flight", port_name(port), live_chains[port], inflight_reads[port], inflight_writes[port]))
      end
      if (requests_launched[port] != requests_completed[port]) begin
        `uvm_fatal("USB_STRESS_ACCOUNTING", $sformatf("%s launched %0d requests but completed %0d", port_name(port), requests_launched[port], requests_completed[port]))
      end
      if (primary_completed[port] != primary_requests || mandatory_completed[port] != mandatory_scheduled[port]) begin
        `uvm_fatal("USB_STRESS_ACCOUNTING", $sformatf("%s completed %0d/%0d chains and %0d/%0d mandatory chains", port_name(port), primary_completed[port], primary_requests, mandatory_completed[port], mandatory_scheduled[port]))
      end
      if (max_inflight_reads[port] < 2 || max_inflight_writes[port] < 2 || !read_write_overlap[port]) begin
        `uvm_fatal("USB_STRESS_CONCURRENCY", $sformatf("%s bus concurrency too low: max accepted reads=%0d writes=%0d read/write overlap=%0b", port_name(port), max_inflight_reads[port], max_inflight_writes[port], read_write_overlap[port]))
      end
    end
    for (int hole = 0; hole < HOLE_COUNT; hole++) begin
      if (hole_completed[hole][0] == 0 || hole_completed[hole][1] == 0) begin
        `uvm_fatal("USB_STRESS_ACCOUNTING", $sformatf("COMBO decode hole %0d 0x%08h..0x%08h completed %0d writes and %0d reads; both are required", hole, HOLE_BASE[hole], HOLE_LIMIT[hole] - 1, hole_completed[hole][0], hole_completed[hole][1]))
      end
    end
    if (max_active_ports != PORT_COUNT) begin
      `uvm_fatal("USB_STRESS_CONCURRENCY", $sformatf("At most %0d of %0d ports had accepted requests outstanding together", max_active_ports, PORT_COUNT))
    end
  endfunction

  // Print per-port request counts, checked beats, concurrency high-water
  // marks, and completed chains by kind, for triage and regression review.
  protected function void report_summary();
    string kinds;
    op_kind_e kind_value;

    for (int unsigned port = 0; port < PORT_COUNT; port++) begin
      kinds = "";
      for (int unsigned kind = 0; kind < OP_KIND_COUNT; kind++) begin
        kind_value = op_kind_e'(kind);
        kinds = {kinds, $sformatf(" %s=%0d", kind_value.name(), kind_completed[port][kind])};
      end
      `uvm_info("USB_STRESS_SUMMARY", $sformatf("%s: requests=%0d/%0d chains=%0d mandatory=%0d/%0d beats_checked=%0d max_live_chains=%0d stress_bus_accepted=%0d max_bus_outstanding reads=%0d writes=%0d total=%0d read/write_overlap=%0b;%s", port_name(port), requests_completed[port], requests_launched[port], primary_completed[port], mandatory_completed[port], mandatory_scheduled[port], beats_checked[port], max_live_chains[port], bus_requests_accepted[port], max_inflight_reads[port], max_inflight_writes[port], max_inflight_total[port], read_write_overlap[port], kinds), UVM_LOW)
    end
    `uvm_info("USB_STRESS_SUMMARY", $sformatf("Max ports with accepted requests outstanding together: %0d/%0d", max_active_ports, PORT_COUNT), UVM_LOW)
    for (int hole = 0; hole < HOLE_COUNT; hole++) begin
      `uvm_info("USB_STRESS_SUMMARY", $sformatf("COMBO decode hole %0d 0x%08h..0x%08h: writes=%0d reads=%0d", hole, HOLE_BASE[hole], HOLE_LIMIT[hole] - 1, hole_completed[hole][0], hole_completed[hole][1]), UVM_LOW)
    end
  endfunction

  // Scenario order: confirm USB is idle, capture CSR state, enable filtering,
  // fill both SRAMs so every word has a known value, run the four-port
  // stress, sweep both SRAMs and recheck CSRs, confirm USB is still idle,
  // restore CSRs with filtering bypassed, then check accounting. completed
  // is set only after every step passes.
  task body();
    completed = 1'b0;
    validate_settings();
    initialize_state();
    check_usb_idle("Start");
    capture_csr_state();
    enable_filtering();
    run_sram_pass(OP_FILL);
    run_stress();
    run_sram_pass(OP_READ);
    check_final_csr_state();
    check_usb_idle("After stress", usb_axi_user_override::with_value(own_user(PORT_COMBO)), usb_axi_user_override::with_value(own_user(PORT_DEV1_CSR)));
    disable_filtering();
    restore_csr_state();
    check_accounting();
    report_summary();
    completed = 1'b1;
    `uvm_info("USB_STRESS", "All chains, full SRAM sweeps, CSR checks, and accounting passed", UVM_LOW)
  endtask
endclass
