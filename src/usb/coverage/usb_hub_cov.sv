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
// AREA: Embedded virtual hub configuration, descriptor write-lock, downstream
// port state and the compound-device function multiplexing.
//
// Plain SystemVerilog passive observer: inputs only, no UVM, no classes, no
// DPI.
//
// ATTACHMENT
// ----------
// This module is NOT bound. Its observation targets live inside the VHDL
// architectures of the compound (usb_ep0_hub_descr, usb_app_hw_hub,
// usb_ep0_handler and the compound structure), and bind cannot target a VHDL
// entity. It is therefore instantiated by a bench-specific probe module that
// supplies the signals through cross-module references, following the
// technique already proven by src/integration/testbench/usb_dev_addr_probe.sv:
//
//   usb_cov_probe_caliptra_ss.sv   drives these ports from
//                                  caliptra_ss_top_tb...u_hub_compound.*
//   (a usb_top_tb equivalent can drive the same ports from its own path)
//
// Keeping the covergroups here and the hierarchy strings in the probe means
// the coverage model itself stays bench-independent: the covergroup and bin
// names are identical whichever probe feeds it, so URG can still merge the two
// databases. Only the thin probe file differs per bench.
//
// Every signal consumed here is a PORT of a VHDL entity, never an internal
// architecture signal, because only ports and port-mapped nets are reliably
// visible to VCS cross-module references in a mixed-language build.
//
// QUESTIONS ANSWERED
// ------------------
//   - Was hub mode both entered and left, and was the hub connected both with
//     and without a valid VBUS session?
//   - Was the descriptor write-lock actually exercised: a descriptor write
//     accepted while unlocked, ignored while locked, AND each lock-exempt
//     register (CONTROL, LPM, ULPIDEBUG) still writable while locked so
//     firmware can release the lock?
//   - Did each downstream port reach connect, enable, suspend, reset and L1,
//     and did each port-status change get reported and cleared?
//   - Were the ports ever independently up and down, which is the hitless
//     update use case?
//   - Which hub class requests were dispatched, to which recipient, and which
//     were rejected with a stall?
//
// NOT COVERED HERE
// ----------------
// Hub descriptor contents, individual table words, and packet-level hub
// behaviour that the USB VIP already checks. The write-lock coverage observes
// the lock's EFFECT on a write, not the data written.
//
// Compound function multiplexing (the shared serial engine and DMA) is NOT
// here either: it is COMPOUND scope rather than HUB scope, so it lives in
// usb_compound_cov.sv. Keeping it out means every covergroup in this file is
// genuinely a hub measurement.
module usb_hub_cov
  import usb_cov_pkg::*;
#(
  parameter int unsigned HUB_PORTS = 2,
  // Mirrors the descriptor table's C_NWORDS. The RTL drops a write at or above
  // this index regardless of the lock state, so that case has to be told apart
  // from a genuine lock-blocked write.
  parameter int unsigned HUB_WORDS = 196
) (
  input logic       clk,
  input logic       rst_n,

  // ---- Hub control register outputs (usb_ep0_hub_descr ports) ----
  input logic       hub_enable,
  input logic       hub_dcon,
  input logic       hub_force_vbus,
  input logic       hub_lpm_sup,
  input logic       hub_force_fs,
  input logic       hub_pll_on,
  input logic       hub_vbusdebounced,
  input logic [1:0] pie_speed,
  input logic       usb_self_powered_ff,

  // ---- Hub table write port (usb_ep0_hub_descr ports) ----
  input logic       reg_write,
  input logic [7:0] reg_waddr,

  // ---- PHY test mode, folded in from the retired E7 group ----
  input logic [2:0] phy_test_mode,

  // ---- Downstream port state (usb_app_hw_hub ports) ----
  input logic [HUB_PORTS-1:0] hub_port_connect,
  input logic [HUB_PORTS-1:0] hub_port_enable,
  input logic [HUB_PORTS-1:0] hub_port_suspend,
  input logic [HUB_PORTS-1:0] hub_port_reset,
  input logic [HUB_PORTS-1:0] hub_port_l1,
  input logic [HUB_PORTS-1:0] hub_port_remotewakeup,

  // ---- Hub status-change IN endpoint (usb_app_hw_hub ports) ----
  input logic       hub_epin_enable_buffer,
  input logic       hub_epin_stall,

  // ---- Hub class request dispatch (usb_app_hw_hub ports) ----
  input logic       ep0_setupdone,
  input logic [6:0] ep0_request,
  input logic [15:0] ep0_wvalue,
  input logic [15:0] ep0_windex,
  input logic       ep0_class_stall,

  // ---- Remote wakeup gate terms (compound structure nets) ----
  input logic       sync_suspend,
  input logic       sync_busreset,
  input logic       ep0_remote_wake_enabled_hub,
  input logic       hub_remotewakeup
);

  // ---------------------------------------------------------------------------
  // Derived observation state
  // ---------------------------------------------------------------------------
  // The descriptor write-lock is the conjunction of hub enable and hub
  // connect. Descriptor and SETUP-table words become read-only while it holds;
  // the exempt registers below stay writable so firmware can always clear
  // connect and release the lock again. Recomputing it from the two published
  // control outputs avoids depending on the internal lock signal.
  logic hub_write_lock;
  always_comb hub_write_lock = hub_enable && hub_dcon;

  hub_word_class_e written_word_class;
  always_comb written_word_class = hub_word_class(reg_waddr, HUB_WORDS);

  // The RTL exempts three words from the lock, not one: CONTROL (word 12),
  // LPM (13) and ULPIDEBUG (15) are always writable, which is what lets
  // firmware release the lock and keep driving LPM and the PHY while the
  // descriptor table is frozen.
  logic written_word_always_writable;
  always_comb begin
    written_word_always_writable =
        (written_word_class == HUB_WORD_CLASS_CONTROL) ||
        (written_word_class == HUB_WORD_CLASS_LPM)     ||
        (written_word_class == HUB_WORD_CLASS_ULPIDEBUG);
  end

  // Classify the outcome of an attempted table write. These outcomes are the
  // whole architectural contract of the lock, and none of them is visible from
  // the bus: a blocked write looks exactly like an accepted one upstream.
  typedef enum int {
    LOCK_WRITE_ACCEPTED_UNLOCKED,  // write while unlocked: must take effect
    LOCK_WRITE_BLOCKED_LOCKED,     // descriptor write while locked: must be ignored
    LOCK_WRITE_EXEMPT_LOCKED,      // CONTROL/LPM/ULPIDEBUG while locked: must still take effect
    LOCK_WRITE_DROPPED_OUT_OF_RANGE // index at or above C_NWORDS: dropped either way
  } lock_write_outcome_e;

  lock_write_outcome_e lock_write_outcome;
  logic                lock_write_event;

  always_comb begin
    lock_write_event = reg_write;
    // The range check is applied first because the RTL ANDs it with the lock
    // exemption, so an out-of-range write is dropped even for an exempt word.
    if (written_word_class == HUB_WORD_CLASS_OUT_OF_RANGE) begin
      lock_write_outcome = LOCK_WRITE_DROPPED_OUT_OF_RANGE;
    end else if (!hub_write_lock) begin
      lock_write_outcome = LOCK_WRITE_ACCEPTED_UNLOCKED;
    end else if (written_word_always_writable) begin
      lock_write_outcome = LOCK_WRITE_EXEMPT_LOCKED;
    end else begin
      lock_write_outcome = LOCK_WRITE_BLOCKED_LOCKED;
    end
  end

  // Why a device-initiated wakeup request did or did not reach the upstream
  // link. The request itself is raised by a device, but in hub mode it is
  // gated by the hub's own host-granted wake enable and by the port being
  // enabled. When the gate is shut the request is discarded with no error and
  // no status bit anywhere, so these bins are the only record that the drop
  // happened and why.
  typedef enum int {
    WAKE_GRANTED,
    WAKE_DROPPED_NOT_SUSPENDED,
    WAKE_DROPPED_WAKE_DISABLED,
    WAKE_DROPPED_PORT_DISABLED
  } wake_outcome_e;

  logic          any_port_wake_request;
  logic          wake_request_event;
  wake_outcome_e wake_outcome;

  always_comb begin
    any_port_wake_request = |hub_port_remotewakeup;
    wake_request_event    = any_port_wake_request;
    if (hub_remotewakeup) begin
      wake_outcome = WAKE_GRANTED;
    end else if (!sync_suspend) begin
      wake_outcome = WAKE_DROPPED_NOT_SUSPENDED;
    end else if (!ep0_remote_wake_enabled_hub) begin
      wake_outcome = WAKE_DROPPED_WAKE_DISABLED;
    end else begin
      wake_outcome = WAKE_DROPPED_PORT_DISABLED;
    end
  end

  // Any downstream port reporting a change. Used to tie a change cause to the
  // status-change endpoint actually being served.
  logic any_port_change_pending;
  always_comb any_port_change_pending = hub_epin_enable_buffer;

  // ---------------------------------------------------------------------------
  // Hub configuration
  // ---------------------------------------------------------------------------
  covergroup usb_hub_config_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = "usb_hub_config";

    // Transitions, because hub mode is documented as set-once during bring-up:
    // the 1 to 0 bin records whether that rule was ever violated, which a
    // level coverpoint could not distinguish from never having been set.
    cp_hub_enable: coverpoint hub_enable iff (rst_n) {
      bins enable_edge  = (1'b0 => 1'b1);
      bins disable_edge = (1'b1 => 1'b0);
    }

    cp_hub_dcon: coverpoint hub_dcon iff (rst_n) {
      bins connect_edge    = (1'b0 => 1'b1);
      bins disconnect_edge = (1'b1 => 1'b0);
    }

    // The effective hub connection is DCON qualified by debounced VBUS, so
    // asserting DCON without VBUS must NOT connect. This cross is the only
    // way to tell the two cases apart.
    cp_vbus_debounced: coverpoint hub_vbusdebounced iff (rst_n);
    cross_dcon_vbus: cross cp_hub_dcon, cp_vbus_debounced;

    // Configuration bits that each have a functional consequence. Covered as
    // transitions so that a bit left at its reset value is visibly uncovered
    // rather than counting as hit.
    cp_force_vbus: coverpoint hub_force_vbus iff (rst_n) {
      bins set_edge   = (1'b0 => 1'b1);
      bins clear_edge = (1'b1 => 1'b0);
    }
    cp_lpm_sup: coverpoint hub_lpm_sup iff (rst_n) {
      bins set_edge   = (1'b0 => 1'b1);
      bins clear_edge = (1'b1 => 1'b0);
    }
    cp_force_fs: coverpoint hub_force_fs iff (rst_n) {
      bins set_edge   = (1'b0 => 1'b1);
      bins clear_edge = (1'b1 => 1'b0);
    }
    cp_pll_on: coverpoint hub_pll_on iff (rst_n) {
      bins set_edge   = (1'b0 => 1'b1);
      bins clear_edge = (1'b1 => 1'b0);
    }
    cp_self_powered: coverpoint usb_self_powered_ff iff (rst_n) {
      bins set_edge   = (1'b0 => 1'b1);
      bins clear_edge = (1'b1 => 1'b0);
    }

    // Forcing full speed must actually produce a full-speed link. Crossing the
    // configuration bit with the negotiated speed is the coverage; the bit on
    // its own only says firmware wrote it.
    cp_speed: coverpoint pie_speed iff (rst_n) {
      bins full_speed = {LINK_SPEED_FS};
      bins high_speed = {LINK_SPEED_HS};
    }
    cross_force_fs_speed: cross cp_force_fs, cp_speed;

    // Folded in from the retired E7 group. PHY test mode is the same kind of
    // question as the bits above - "which configuration was the hub ever run
    // in" - so it belongs here rather than in a group of its own. Only the
    // normal-operation and the defined test encodings are binned; the rest of
    // the 3-bit space is unassigned in the IP.
    cp_phy_test_mode: coverpoint phy_test_mode iff (rst_n) {
      bins normal     = {3'd0};
      bins test_j     = {3'd1};
      bins test_k     = {3'd2};
      bins test_se0   = {3'd3};
      bins test_packet= {3'd4};
      bins other      = default;
    }
    cross_mode_speed: cross cp_phy_test_mode, cp_speed;
  endgroup

  // ---------------------------------------------------------------------------
  // Descriptor write-lock
  // ---------------------------------------------------------------------------
  covergroup usb_hub_write_lock_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = "usb_hub_write_lock";

    cp_outcome: coverpoint lock_write_outcome iff (rst_n && lock_write_event);

    cp_word_class: coverpoint written_word_class iff (rst_n && lock_write_event);

    // The headline cross of this area: which word classes were written in
    // which lock state. The required hits are a descriptor word accepted while
    // unlocked, the same class blocked while locked, and each lock-exempt
    // register still accepted while locked.
    cross_outcome_word_class: cross cp_outcome, cp_word_class;
  endgroup

  // ---------------------------------------------------------------------------
  // Downstream port state
  // ---------------------------------------------------------------------------
  // Generated per port so the bin names carry the port index, which keeps the
  // report readable and lets a one-port-only gap be spotted immediately.
  generate
    for (genvar port_idx = 0; port_idx < HUB_PORTS; port_idx++) begin : gen_port_cov

      covergroup usb_hub_port_cg @(posedge clk);
        option.per_instance = 1;
        option.name         = $sformatf("usb_hub_port%0d", port_idx);

        cp_connect: coverpoint hub_port_connect[port_idx] iff (rst_n) {
          bins connect_edge    = (1'b0 => 1'b1);
          bins disconnect_edge = (1'b1 => 1'b0);
        }
        cp_enable: coverpoint hub_port_enable[port_idx] iff (rst_n) {
          bins enable_edge  = (1'b0 => 1'b1);
          bins disable_edge = (1'b1 => 1'b0);
        }
        cp_suspend: coverpoint hub_port_suspend[port_idx] iff (rst_n) {
          bins suspend_edge = (1'b0 => 1'b1);
          bins resume_edge  = (1'b1 => 1'b0);
        }
        cp_reset: coverpoint hub_port_reset[port_idx] iff (rst_n) {
          bins reset_assert_edge   = (1'b0 => 1'b1);
          bins reset_deassert_edge = (1'b1 => 1'b0);
        }
        cp_l1: coverpoint hub_port_l1[port_idx] iff (rst_n) {
          bins l1_enter_edge = (1'b0 => 1'b1);
          bins l1_exit_edge  = (1'b1 => 1'b0);
        }

        // A port enabled without a connected device is architecturally
        // impossible, so this cross doubles as a cheap sanity observation.
        cp_connect_level: coverpoint hub_port_connect[port_idx] iff (rst_n);
        cp_enable_level:  coverpoint hub_port_enable[port_idx] iff (rst_n);
        cross_connect_enable: cross cp_connect_level, cp_enable_level;

        // Suspending a port that is not enabled has no effect, so the state in
        // which the suspend happened is part of the question.
        cross_suspend_enable: cross cp_suspend, cp_enable_level;
      endgroup

      usb_hub_port_cg usb_hub_port_cg_inst = new();

    end : gen_port_cov
  endgenerate

  // Port independence is a property of the port VECTOR, not of one port, so it
  // is covered once rather than per port. The two mixed bins are the hitless
  // update use case: one device cycles while the other stays enumerated.
  covergroup usb_hub_port_independence_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = "usb_hub_port_independence";

    cp_connect_pattern: coverpoint hub_port_connect iff (rst_n) {
      bins both_down     = {2'b00};
      bins port1_only    = {2'b01};
      bins port2_only    = {2'b10};
      bins both_up       = {2'b11};
      bins port2_cycles  = (2'b11 => 2'b01 => 2'b11);
      bins port1_cycles  = (2'b11 => 2'b10 => 2'b11);
    }

    cp_enable_pattern: coverpoint hub_port_enable iff (rst_n) {
      bins both_disabled = {2'b00};
      bins port1_only    = {2'b01};
      bins port2_only    = {2'b10};
      bins both_enabled  = {2'b11};
    }
  endgroup

  // ---------------------------------------------------------------------------
  // Hub status-change reporting
  // ---------------------------------------------------------------------------
  covergroup usb_hub_status_change_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = "usb_hub_status_change";

    // The status-change interrupt IN endpoint is how the host learns anything
    // changed. Covering the buffer being enabled proves a change was actually
    // reported, not merely latched internally.
    cp_change_reported: coverpoint any_port_change_pending iff (rst_n) {
      bins report_edge = (1'b0 => 1'b1);
      bins clear_edge  = (1'b1 => 1'b0);
    }

    // A halted status-change endpoint is a distinct functional state that the
    // host must recover from with a clear-feature.
    cp_epin_stall: coverpoint hub_epin_stall iff (rst_n) {
      bins stall_edge   = (1'b0 => 1'b1);
      bins unstall_edge = (1'b1 => 1'b0);
    }

    // E6: the buffer-enable level, as opposed to the change edges above.
    // Crossing it with the stall tells halt-while-armed apart from
    // halt-while-idle, which is what the hub_endpoint_halt tests set up: a
    // halt taken with a change already pending must not lose the change.
    cp_epin_enable_buffer: coverpoint hub_epin_enable_buffer iff (rst_n);
    cross_stall_armed: cross cp_epin_stall, cp_epin_enable_buffer;
  endgroup

  // ---------------------------------------------------------------------------
  // Hub class request dispatch
  // ---------------------------------------------------------------------------
  covergroup usb_hub_class_req_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = "usb_hub_class_req";

    // The three hub class operations the hardware implements, plus the LPM
    // set-and-test. Values are the C_CLASS_REQ_* encodings.
    cp_request: coverpoint ep0_request iff (rst_n && ep0_setupdone) {
      bins clear_feature = {7'h40};
      bins set_feature   = {7'h41};
      bins get_status    = {7'h42};
      bins set_and_test  = {7'h43};
    }

    // Recipient class taken from the low byte of wIndex: zero addresses the
    // hub itself, one and two the downstream ports, anything higher is out of
    // range and must be stalled.
    cp_recipient: coverpoint ep0_windex[7:0] iff (rst_n && ep0_setupdone) {
      bins hub       = {8'd0};
      bins port1     = {8'd1};
      bins port2     = {8'd2};
      bins port_oor  = {[8'd3:8'd255]};
    }

    // Feature selectors. Each takes a different leg in the hub FSM, and the
    // unsupported selector must produce a stall, so the reject case is a bin
    // of its own rather than an omission.
    cp_feature: coverpoint ep0_wvalue[7:0] iff (rst_n && ep0_setupdone) {
      bins port_connection      = {8'd0};
      bins port_enable          = {8'd1};
      bins port_suspend         = {8'd2};
      bins port_overcurrent     = {8'd3};
      bins port_reset           = {8'd4};
      bins port_l1              = {8'd10};
      bins c_port_connection    = {8'd16};
      bins c_port_suspend       = {8'd18};
      bins c_port_reset         = {8'd20};
      bins c_port_l1            = {8'd23};
      bins unsupported          = default;
    }

    // Accept versus stall is the outcome that matters; without it a covered
    // request does not tell you whether the hub honoured or rejected it.
    cp_stall: coverpoint ep0_class_stall iff (rst_n && ep0_setupdone) {
      bins accepted = {1'b0};
      bins stalled  = {1'b1};
    }

    cross_request_recipient: cross cp_request, cp_recipient;
    cross_feature_stall:     cross cp_feature, cp_stall;
  endgroup

  // ---------------------------------------------------------------------------
  // Remote wakeup gate
  // ---------------------------------------------------------------------------
  // The hub gates a device-initiated wakeup on its own host-granted wake
  // enable and on the port being enabled. Each drop reason is completely
  // silent externally, so these bins are the only evidence of which path a
  // request actually took.
  covergroup usb_hub_remote_wakeup_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = "usb_hub_remote_wakeup";

    cp_outcome: coverpoint wake_outcome iff (rst_n && wake_request_event);

    cp_wake_enabled: coverpoint ep0_remote_wake_enabled_hub iff (rst_n);
    cp_suspended:    coverpoint sync_suspend iff (rst_n);

    // The gate's full AND-term matrix. A granted wakeup requires suspend and
    // the host-granted enable together; the cross shows which combinations the
    // stimulus actually produced.
    cross_gate_terms: cross cp_wake_enabled, cp_suspended, cp_outcome;

    // A bus reset clears the host-granted wake enable, so a wake request
    // issued after a reset but before a fresh set-feature is dropped. Covering
    // the clearing edge records that this ordering hazard was reached.
    cp_wake_enable_cleared: coverpoint ep0_remote_wake_enabled_hub iff (rst_n) {
      bins granted_edge = (1'b0 => 1'b1);
      bins cleared_edge = (1'b1 => 1'b0);
    }
    cp_busreset: coverpoint sync_busreset iff (rst_n) {
      bins reset_edge = (1'b0 => 1'b1);
    }
  endgroup

  usb_hub_config_cg            usb_hub_config_cg_inst            = new();
  usb_hub_write_lock_cg        usb_hub_write_lock_cg_inst        = new();
  usb_hub_port_independence_cg usb_hub_port_independence_cg_inst = new();
  usb_hub_status_change_cg     usb_hub_status_change_cg_inst     = new();
  usb_hub_class_req_cg         usb_hub_class_req_cg_inst         = new();
  usb_hub_remote_wakeup_cg     usb_hub_remote_wakeup_cg_inst     = new();

endmodule : usb_hub_cov

// File contains AI-generated response based on internal company sources
