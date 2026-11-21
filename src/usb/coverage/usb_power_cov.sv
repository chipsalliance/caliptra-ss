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
// AREA H: clock gating and UTMI reset context, observed at the compound
// boundary, plus the narrow OCP recovery claim handshake.
//
// SCOPE NOTE - WHY THIS FILE IS SMALL
// -----------------------------------
// This file used to also carry interrupt delivery, suspend/resume state and
// topology configuration. All three are now measured where they are actually
// attributable:
//
//   - interrupt delivery  -> usb_dev_ep_cov  (area D, per device)
//   - suspend / resume    -> usb_dev_link_cov (areas A1/A2/A4, per device)
//   - VBUS session        -> usb_dev_enum_cov (area B2, per device) and the
//                            reset-context cross below
//   - topology / speed    -> usb_hub_cov (area E) and usb_compound_cov (F1)
//
// The reason for moving them is attribution, not tidiness: the wrapper ports
// this file can see are the MERGED subsystem-level view, so a suspend observed
// here cannot be told apart between dev0 and dev1. The per-device observers
// read usb_reg_if_1/_2 and therefore can. What remains here is exactly what is
// genuinely subsystem-wide: there is one clock request and one UTMI reset for
// the whole compound, so those have no per-device form.
//
// Plain SystemVerilog passive observer: inputs only, no UVM, no classes, no
// DPI. It is attached with bind, so no design file is modified.
//
// ATTACHMENT
// ----------
// Bound by MODULE TYPE to ip_xxx_3511_hs_mem_compound_wrapper (see
// usb_cov_bind.sv). Every signal used here is a PORT of that wrapper, so the
// bind resolves all port expressions in the wrapper's own scope and this file
// contains no hierarchy path. The wrapper is instantiated in both the
// subsystem bench and the compound unit bench, which makes the covergroup and
// bin names identical in the two coverage databases and lets URG merge them
// directly.
//
// QUESTIONS ANSWERED
// ------------------
//   - Was the clock request ever RELEASED, or does it stay asserted for the
//     whole run because FORCE_NEEDCLK masks it permanently? A release that
//     never happens means the clock-gating handshake is entirely unverified.
//   - Was the release taken in the state where it matters, i.e. while the
//     link was suspended?
//   - Was a reset ever taken while the subsystem was busy rather than idle,
//     and with VBUS valid rather than absent?
//   - Did the OCP recovery claim handshake complete?
//
// NOT COVERED HERE
// ----------------
// UTMI data buses, PID or packet structure, chirp timing: all USB VIP
// territory. Only the subsystem-visible consequences of those events are
// sampled. Link speed is read from the PHY select pins rather than from a
// register, because those pins are what the subsystem actually drives.
module usb_power_cov
  import usb_cov_pkg::*;
(
  input logic       clk,
  input logic       rst_n,

  // ---- OCP recovery sideband ----
  input logic       payload_available,
  input logic       ocp_firmware_activated,

  // ---- Power, clock request and session ----
  input logic       usb_vbus,
  input logic       usb_needclk,

  // ---- Link state as driven onto the PHY ----
  input logic       utmi_suspendm,
  input logic       utmi_reset,
  input logic       utmi_txvalid,
  input logic [1:0] utmi_linestate
);

  // ---------------------------------------------------------------------------
  // Derived observation state
  // ---------------------------------------------------------------------------
  // Suspend is observed as SuspendM deasserted, which is the subsystem-visible
  // consequence of the link entering a low-power state. Using the PHY-facing
  // pin rather than an internal net keeps this module free of any VHDL
  // dependency and therefore mergeable across the two benches.
  //
  // bus_active is "the subsystem is doing something on the wire": either it is
  // transmitting, or the line is not sitting at idle J. It is the qualifier
  // that turns a bare reset into a meaningful scenario.
  logic suspended;
  logic bus_active;

  always_comb begin
    suspended  = !utmi_suspendm;
    bus_active = utmi_txvalid || (utmi_linestate != 2'b01);
  end

  // ---------------------------------------------------------------------------
  // Clock request
  // ---------------------------------------------------------------------------
  // The interesting outcome is the RELEASE. If FORCE_NEEDCLK is set during
  // bring-up and never cleared, needclk stays high for the whole run and the
  // clock-gating handshake is never exercised at all. Crossing with suspend
  // shows whether the release happened in the state where it matters.
  covergroup usb_clock_request_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = "usb_clock_request";

    cp_needclk: coverpoint usb_needclk iff (rst_n) {
      bins request_edge = (1'b0 => 1'b1);
      bins release_edge = (1'b1 => 1'b0);
    }

    cp_suspended: coverpoint suspended iff (rst_n);

    cross_needclk_suspend: cross cp_needclk, cp_suspended;
  endgroup

  // ---------------------------------------------------------------------------
  // Reset context
  // ---------------------------------------------------------------------------
  // A reset taken at time zero is free. A reset taken while the subsystem was
  // transmitting, or while VBUS was valid and the link was up, is the case
  // that exercises the recovery path. The cross records which contexts were
  // actually reached.
  covergroup usb_reset_context_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = "usb_reset_context";

    cp_utmi_reset: coverpoint utmi_reset iff (rst_n) {
      bins assert_edge   = (1'b0 => 1'b1);
      bins deassert_edge = (1'b1 => 1'b0);
    }

    cp_context_vbus: coverpoint usb_vbus iff (rst_n);
    cp_context_busy: coverpoint bus_active iff (rst_n);

    cross_reset_context: cross cp_utmi_reset, cp_context_vbus, cp_context_busy;
  endgroup

  // ---------------------------------------------------------------------------
  // OCP recovery claim
  // ---------------------------------------------------------------------------
  // Narrow on purpose. The OCP recovery sequences already carry their own
  // covergroups for image, FIFO and collision behaviour, so only the
  // subsystem-visible claim handshake is sampled here to avoid duplicating
  // coverage that already exists.
  covergroup usb_ocp_claim_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = "usb_ocp_claim";

    cp_payload_available: coverpoint payload_available iff (rst_n) {
      bins assert_edge   = (1'b0 => 1'b1);
      bins deassert_edge = (1'b1 => 1'b0);
    }

    cp_firmware_activated: coverpoint ocp_firmware_activated iff (rst_n) {
      bins activate_edge = (1'b0 => 1'b1);
    }
  endgroup

  usb_clock_request_cg usb_clock_request_cg_inst = new();
  usb_reset_context_cg usb_reset_context_cg_inst = new();
  usb_ocp_claim_cg     usb_ocp_claim_cg_inst     = new();

endmodule : usb_power_cov

// File contains AI-generated response based on internal company sources
