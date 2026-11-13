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
// AREA A: device link power state (L0 / L1 / L2 / disconnected).
//
// Plain SystemVerilog passive observer: inputs only, no UVM, no classes, no
// DPI. One instance per device, so DEV0 and DEV1 report separately instead of
// being averaged together.
//
// ATTACHMENT
// ----------
// Fed by the bench probe from the per-device VHDL register file usb_reg_if_N.
// A bind cannot reach into a VHDL entity, so the hierarchy paths live in
// src/integration/testbench/usb_cov_probe_caliptra_ss.sv and this file stays
// bench-independent: a usb_top_tb probe can drive the identical port list and
// URG will merge the two databases.
//
// WHY THESE SIGNALS
// -----------------
// Every input is one of the DEVCMDSTAT fields the register genuinely returns
// to firmware, taken from the SYNCHRONISED side of the IP (sync_suspend,
// sync_lpm_Suspend, sync_lpm_rw). Coverage therefore reflects what a test can
// actually observe through the register, not an internal pre-sync value.
//
// QUESTIONS ANSWERED
// ------------------
//   - Was each link state entered, and at which speed?
//   - Were the legal state transitions exercised, and did any illegal one
//     occur?
//   - Was L1 entered, and HOW was it left: host resume, device-initiated
//     wakeup, or bus reset? Device-initiated is the hard path.
//   - Did the LPM HIRD token programmed by firmware match what the hardware
//     reloaded from the host's LPM transaction?
//   - Was L2 ever entered while the clock was still being force-requested?
//
// ILLEGAL BINS
// ------------
// Transitions that the architecture forbids are given explicit bins named
// illegal_*. They are NOT SystemVerilog illegal_bins, which would kill the
// simulation; a plain bin records the violation so it shows up in the report
// and can be filtered by name. A non-zero illegal_* bin is a failure signal,
// not a coverage hole.
module usb_dev_link_cov
  import usb_cov_pkg::*;
#(
  // Carried into option.name so DEV0 and DEV1 are distinguishable in the
  // report while the covergroup TYPE stays identical for merging.
  parameter string DEV_NAME = "dev0"
) (
  input logic       clk,
  input logic       rst_n,

  // DEVCMDSTAT status bits (usb_reg_if_N).
  input logic       dcon,          // bit 16, usbreg_dev_connect
  input logic       dsus,          // bit 17, sync_suspend
  input logic       lpm_sus,       // bit 19, sync_lpm_Suspend
  input logic       lpm_rewp,      // bit 20, sync_lpm_rw: host granted bRemoteWake
  input logic [1:0] speed,         // bits 23:22, pie_speed

  // Wakeup request strobes driven by a DEVCMDSTAT write.
  input logic       remotewakeup,     // usbreg_remotewakeup, L2 exit request
  input logic       lpm_remotewakeup, // usbreg_lpmremotewakeup, L1 exit request

  // Bus reset, which exits either low-power state.
  input logic       busreset,      // sync_busreset

  // LPM token round trip: firmware programs HIRD, hardware reloads it from
  // the host's LPM transaction.
  input logic [3:0] lpm_hird_sw,   // usbreg_lpm_hird_sw
  input logic [3:0] lpm_hird_hw,   // sieint_lpm_hird_hw
  input logic       lpm_nyet,      // usbreg_lpm_nyet: refuse the LPM request

  // Clock request, needed to catch a suspend entered with the clock forced.
  input logic       force_needclk, // usbreg_pll_on

  // VBUS, which distinguishes a power-loss exit from a protocol exit.
  input logic       vbus_debounced // sync_VBusDebounced
);

  // ---------------------------------------------------------------------------
  // Link state and its history
  // ---------------------------------------------------------------------------
  link_state_e state;
  link_state_e state_q;

  always_comb state = link_state(dcon, dsus, lpm_sus);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) state_q <= LINK_STATE_DISCONNECTED;
    else        state_q <= state;
  end

  // A transition sample is only meaningful on the cycle the state actually
  // changes; sampling every cycle would bury the transitions under self-loops.
  logic state_changed;
  always_comb state_changed = (state != state_q);

  // ---------------------------------------------------------------------------
  // Low-power exit cause
  // ---------------------------------------------------------------------------
  // Decided from the state we LEFT and the strobes present at that moment.
  // The register-write strobes are what the firmware helpers drive, so this
  // distinguishes a device-initiated wakeup from a host-driven resume rather
  // than inferring it from the state change alone.
  lp_exit_cause_e l1_exit_cause;
  lp_exit_cause_e l2_exit_cause;
  logic           l1_exit_event;
  logic           l2_exit_event;

  always_comb begin
    l1_exit_event = state_changed && (state_q == LINK_STATE_L1_SLEEP);
    l2_exit_event = state_changed && (state_q == LINK_STATE_L2_SUSPEND);

    // Bus reset is checked first: it overrides any pending wakeup request.
    if (busreset) begin
      l1_exit_cause = LP_EXIT_BUSRESET;
    end else if (lpm_remotewakeup) begin
      l1_exit_cause = LP_EXIT_DEVICE_WAKEUP;
    end else begin
      l1_exit_cause = LP_EXIT_HOST_RESUME;
    end

    if (busreset) begin
      l2_exit_cause = LP_EXIT_BUSRESET;
    end else if (!vbus_debounced) begin
      // Losing VBUS is a power event, not a protocol resume.
      l2_exit_cause = LP_EXIT_VBUS_LOSS;
    end else if (remotewakeup) begin
      l2_exit_cause = LP_EXIT_DEVICE_WAKEUP;
    end else begin
      l2_exit_cause = LP_EXIT_HOST_RESUME;
    end
  end

  // Entry edges, registered so the entry condition can be crossed with the
  // state that applied when the entry happened.
  logic l1_entry_event;
  logic l2_entry_event;
  logic force_needclk_at_l2_entry;

  always_comb begin
    l1_entry_event = state_changed && (state == LINK_STATE_L1_SLEEP);
    l2_entry_event = state_changed && (state == LINK_STATE_L2_SUSPEND);
  end

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)              force_needclk_at_l2_entry <= 1'b0;
    else if (l2_entry_event) force_needclk_at_l2_entry <= force_needclk;
  end

  // ---------------------------------------------------------------------------
  // A1: link state and transitions
  // ---------------------------------------------------------------------------
  covergroup usb_link_state_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = {"usb_link_state_", DEV_NAME};

    cp_state: coverpoint state iff (rst_n);

    // Only the architecturally reachable transitions get named bins. The
    // illegal_* bins below should never be hit; a hit is a real finding.
    cp_transition: coverpoint state iff (rst_n && state_changed) {
      bins enter_l1 = (LINK_STATE_L0_ACTIVE  => LINK_STATE_L1_SLEEP);
      bins exit_l1  = (LINK_STATE_L1_SLEEP   => LINK_STATE_L0_ACTIVE);
      bins enter_l2 = (LINK_STATE_L0_ACTIVE  => LINK_STATE_L2_SUSPEND);
      bins exit_l2  = (LINK_STATE_L2_SUSPEND => LINK_STATE_L0_ACTIVE);
      bins connect     = (LINK_STATE_DISCONNECTED => LINK_STATE_L0_ACTIVE);
      bins disconnect  = (LINK_STATE_L0_ACTIVE    => LINK_STATE_DISCONNECTED);

      // A device cannot hop between the two low-power states without
      // returning to L0 first, and it cannot resume straight out of a
      // disconnect into a low-power state.
      bins illegal_l1_to_l2   = (LINK_STATE_L1_SLEEP => LINK_STATE_L2_SUSPEND);
      bins illegal_l2_to_l1   = (LINK_STATE_L2_SUSPEND => LINK_STATE_L1_SLEEP);
      bins illegal_disc_to_l1 = (LINK_STATE_DISCONNECTED => LINK_STATE_L1_SLEEP);
      bins illegal_disc_to_l2 = (LINK_STATE_DISCONNECTED => LINK_STATE_L2_SUSPEND);
    }

    cp_speed: coverpoint speed iff (rst_n) {
      bins full_speed = {LINK_SPEED_FS};
      bins high_speed = {LINK_SPEED_HS};
    }

    // The headline crosses of this area. A state or transition verified at HS
    // says nothing about FS: the resume timing and the chirp differ, and the
    // suite has separate fs_* and hs_* tests precisely for that reason.
    cross_state_speed:      cross cp_state, cp_speed;
    cross_transition_speed: cross cp_transition, cp_speed;
  endgroup

  // ---------------------------------------------------------------------------
  // A2: LPM / L1 sleep, including the HIRD token round trip
  // ---------------------------------------------------------------------------
  covergroup usb_lpm_l1_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = {"usb_lpm_l1_", DEV_NAME};

    cp_l1_entry: coverpoint l1_entry_event iff (rst_n) {
      bins entered = {1'b1};
    }

    // A coverpoint is local to its covergroup, so each group that wants to
    // cross against speed declares its own.
    cp_speed_l1: coverpoint speed iff (rst_n) {
      bins full_speed = {LINK_SPEED_FS};
      bins high_speed = {LINK_SPEED_HS};
    }

    // The question is not that L1 ended but which mechanism ended it.
    // LP_EXIT_VBUS_LOSS is excluded: an L1 exit is a protocol event, and a
    // VBUS drop would be reported as a disconnect instead.
    cp_l1_exit_cause: coverpoint l1_exit_cause iff (rst_n && l1_exit_event) {
      bins host_resume   = {LP_EXIT_HOST_RESUME};
      bins device_wakeup = {LP_EXIT_DEVICE_WAKEUP};
      bins busreset      = {LP_EXIT_BUSRESET};
    }

    // Host-granted bRemoteWake. The device may only drive an L1 wakeup when
    // this is set, which the cross below checks.
    cp_rewp: coverpoint lpm_rewp iff (rst_n);

    // NYET means the device refused the LPM request, which is a legal answer
    // and a distinct scenario from accepting it.
    cp_nyet: coverpoint lpm_nyet iff (rst_n) {
      bins accepted = {1'b0};
      bins refused  = {1'b1};
    }

    // HIRD / BESL token. cp_hird_sw records which values firmware programmed;
    // cp_hird_hw_match records whether the value the hardware reloaded from
    // the host's LPM transaction agreed with it. A mismatch bin hit means the
    // token did not round-trip.
    cp_hird_sw: coverpoint lpm_hird_sw iff (rst_n);

    cp_hird_hw_match: coverpoint (lpm_hird_sw == lpm_hird_hw)
                      iff (rst_n && lpm_sus) {
      bins match    = {1'b1};
      bins mismatch = {1'b0};
    }

    // A device-initiated wakeup with bRemoteWake not granted is a protocol
    // violation, so the device_wakeup x rewp=0 bin of this cross is the
    // interesting one: it should stay empty.
    cross_exit_rewp: cross cp_l1_exit_cause, cp_rewp;

    // L1 must be proven at both speeds; the suite has fs_ and hs_ L1 tests.
    cross_l1_speed: cross cp_l1_entry, cp_speed_l1;

    // Ties the programmed HIRD to an actual L1 entry, so a HIRD value that
    // was written but never used in a real L1 does not count as covered.
    cross_hird_entry: cross cp_hird_sw, cp_l1_entry;
  endgroup

  // ---------------------------------------------------------------------------
  // A4: L2 suspend and resume
  // ---------------------------------------------------------------------------
  covergroup usb_l2_suspend_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = {"usb_l2_suspend_", DEV_NAME};

    cp_l2_entry: coverpoint l2_entry_event iff (rst_n) {
      bins entered = {1'b1};
    }

    cp_speed_l2: coverpoint speed iff (rst_n) {
      bins full_speed = {LINK_SPEED_FS};
      bins high_speed = {LINK_SPEED_HS};
    }

    cp_l2_exit_cause: coverpoint l2_exit_cause iff (rst_n && l2_exit_event) {
      bins host_resume   = {LP_EXIT_HOST_RESUME};
      bins device_wakeup = {LP_EXIT_DEVICE_WAKEUP};
      bins busreset      = {LP_EXIT_BUSRESET};
      bins vbus_loss     = {LP_EXIT_VBUS_LOSS};
    }

    // Entering suspend while the clock is still force-requested is the
    // classic bring-up bug: the link reports suspend but the PLL never stops,
    // so the power saving never happens. Recorded at the entry edge because
    // the level afterwards says nothing about the entry.
    cp_needclk_at_entry: coverpoint force_needclk_at_l2_entry
                         iff (rst_n && l2_entry_event) {
      bins clock_released = {1'b0};
      bins clock_forced   = {1'b1};
    }

    cross_exit_speed:    cross cp_l2_exit_cause, cp_speed_l2;
    cross_entry_needclk: cross cp_l2_entry, cp_needclk_at_entry;
  endgroup

  usb_link_state_cg  usb_link_state_cg_inst  = new();
  usb_lpm_l1_cg      usb_lpm_l1_cg_inst      = new();
  usb_l2_suspend_cg  usb_l2_suspend_cg_inst  = new();

endmodule : usb_dev_link_cov

// File contains AI-generated response based on internal company sources
