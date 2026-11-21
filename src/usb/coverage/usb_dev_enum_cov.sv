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
// AREA B: device enumeration, connection and bus reset.
//
// Plain SystemVerilog passive observer: inputs only, no UVM, no classes, no
// DPI. One instance per device, fed by the bench probe from the per-device
// VHDL register file usb_reg_if_N (a bind cannot target a VHDL entity).
//
// QUESTIONS ANSWERED
// ------------------
//   - Did SET_ADDRESS actually take effect, and was enumeration completed at
//     both speeds?
//   - Were connect AND disconnect both exercised, and was a connect ever
//     asserted without debounced VBUS?
//   - Was a bus reset seen from each link state, and did it clear the device
//     address as the spec requires?
//   - Did forcing full speed actually produce a full-speed link, and do the
//     UTMI transceiver selects agree with the reported speed?
//
// WHY ADDRESS IS OBSERVED AS A CLASS, NOT A VALUE
// -----------------------------------------------
// The specific address a host assigns is arbitrary; what matters
// architecturally is the zero to non-zero transition, because that is the
// point at which the device leaves the default state. Binning all 127 values
// would add bins without adding information.
module usb_dev_enum_cov
  import usb_cov_pkg::*;
#(
  parameter string DEV_NAME = "dev0"
) (
  input logic       clk,
  input logic       rst_n,

  // DEVCMDSTAT fields (usb_reg_if_N).
  input logic [6:0] dev_addr,       // bits 6:0,   usbreg_usbaddress
  input logic       dev_en,         // bit 7,      usbreg_deviceenabled
  input logic       setup,          // bit 8,      usbreg_setup
  input logic       dcon,           // bit 16,     usbreg_dev_connect
  input logic       dsus,           // bit 17,     sync_suspend
  input logic       lpm_sus,        // bit 19,     sync_lpm_Suspend
  input logic       force_fs,       // bit 21,     usbreg_port_force_fullspeed
  input logic [1:0] speed,          // bits 23:22, pie_speed
  input logic       vbus_debounced, // bit 28,     sync_VBusDebounced

  input logic       busreset,       // sync_busreset

  // UTMI transceiver configuration, which is how the speed decision is
  // actually driven onto the PHY. Shared PIE outputs, but the link they
  // describe is the one this device is using when it is the selected
  // function, so they are meaningful alongside the per-device speed field.
  input logic       utmi_xcvrselect,
  input logic       utmi_termselect
);

  // ---------------------------------------------------------------------------
  // Address assignment
  // ---------------------------------------------------------------------------
  // Classified rather than binned per value: the architectural event is
  // leaving the default address, not which address was chosen.
  typedef enum int {
    ADDR_DEFAULT,    // zero: the device is in its default state
    ADDR_ASSIGNED    // non-zero: a SET_ADDRESS has taken effect
  } addr_state_e;

  addr_state_e addr_state;
  addr_state_e addr_state_q;

  always_comb addr_state = (dev_addr == 7'd0) ? ADDR_DEFAULT : ADDR_ASSIGNED;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) addr_state_q <= ADDR_DEFAULT;
    else        addr_state_q <= addr_state;
  end

  // ---------------------------------------------------------------------------
  // Bus reset context
  // ---------------------------------------------------------------------------
  // The link state a reset arrives in decides which recovery path the IP
  // takes, so the state is captured at the reset edge rather than sampled
  // afterwards, by which time it has already changed.
  link_state_e state;
  logic        busreset_q;
  logic        busreset_edge;
  link_state_e reset_from_state;

  always_comb state = link_state(dcon, dsus, lpm_sus);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) busreset_q <= 1'b0;
    else        busreset_q <= busreset;
  end

  always_comb busreset_edge = busreset && !busreset_q;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)             reset_from_state <= LINK_STATE_DISCONNECTED;
    else if (busreset_edge) reset_from_state <= state;
  end

  // A bus reset must return the device to the default address. This tracks
  // whether a reset was followed by the address actually dropping to zero,
  // which a level coverpoint on the address could not distinguish from the
  // device never having been addressed at all.
  logic addr_cleared_by_reset;
  logic reset_seen_while_addressed;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      reset_seen_while_addressed <= 1'b0;
      addr_cleared_by_reset      <= 1'b0;
    end else begin
      if (busreset_edge && (addr_state == ADDR_ASSIGNED)) begin
        reset_seen_while_addressed <= 1'b1;
      end
      // The clearing edge: previously addressed, now back to default.
      if (reset_seen_while_addressed &&
          (addr_state_q == ADDR_ASSIGNED) && (addr_state == ADDR_DEFAULT)) begin
        addr_cleared_by_reset      <= 1'b1;
        reset_seen_while_addressed <= 1'b0;
      end
    end
  end

  // ---------------------------------------------------------------------------
  // B1: enumeration
  // ---------------------------------------------------------------------------
  covergroup usb_enum_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = {"usb_enum_", DEV_NAME};

    // Both levels plus the assignment edge. The edge is the real event; the
    // levels give the cross below something stable to work against.
    cp_addr_assigned: coverpoint addr_state iff (rst_n) {
      bins default_addr  = {ADDR_DEFAULT};
      bins assigned_addr = {ADDR_ASSIGNED};
      bins assign_edge   = (ADDR_DEFAULT => ADDR_ASSIGNED);
      bins clear_edge    = (ADDR_ASSIGNED => ADDR_DEFAULT);
    }

    // Device enable is firmware bringing the function up; both directions
    // matter because the disable path is used by the disconnect tests.
    cp_dev_en: coverpoint dev_en iff (rst_n) {
      bins enable_edge  = (1'b0 => 1'b1);
      bins disable_edge = (1'b1 => 1'b0);
    }

    // A SETUP packet having been received at all. Without this, an
    // enumeration score would be meaningless: no SETUP means no control
    // transfer ever reached the device.
    cp_setup: coverpoint setup iff (rst_n) {
      bins setup_received = (1'b0 => 1'b1);
    }

    cp_speed: coverpoint speed iff (rst_n) {
      bins full_speed = {LINK_SPEED_FS};
      bins high_speed = {LINK_SPEED_HS};
    }

    // Enumeration must be proven at both speeds, which is why the suite has
    // parallel fs_ and hs_ enumeration tests.
    cross_enum_speed: cross cp_addr_assigned, cp_speed;
  endgroup

  // ---------------------------------------------------------------------------
  // B2: connection and VBUS
  // ---------------------------------------------------------------------------
  covergroup usb_connect_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = {"usb_connect_", DEV_NAME};

    // Disconnect is as important as connect: the suite has dedicated
    // disconnect and hotplug tests, and the teardown path is where state
    // tends to be left behind.
    cp_dcon: coverpoint dcon iff (rst_n) {
      bins connect_edge    = (1'b0 => 1'b1);
      bins disconnect_edge = (1'b1 => 1'b0);
    }

    cp_vbus_debounced: coverpoint vbus_debounced iff (rst_n);

    // Asserting connect without debounced VBUS is the self-powered /
    // VBUS-absent boot scenario, and also a plausible firmware mistake. The
    // cross is the measurement; the bare edge is only its precondition.
    cross_dcon_vbus: cross cp_dcon, cp_vbus_debounced;
  endgroup

  // ---------------------------------------------------------------------------
  // B3: bus reset
  // ---------------------------------------------------------------------------
  covergroup usb_reset_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = {"usb_reset_", DEV_NAME};

    cp_busreset: coverpoint busreset_edge iff (rst_n) {
      bins reset_seen = {1'b1};
    }

    // Reset out of L0, L1 and L2 are three different recovery paths in the
    // IP, so "a reset happened" does not answer whether they were all taken.
    cp_reset_from_state: coverpoint reset_from_state iff (rst_n && busreset_edge);

    // Did the reset actually clear the address, as the spec requires.
    cp_addr_cleared: coverpoint addr_cleared_by_reset iff (rst_n) {
      bins cleared = (1'b0 => 1'b1);
    }

    cp_speed_rst: coverpoint speed iff (rst_n) {
      bins full_speed = {LINK_SPEED_FS};
      bins high_speed = {LINK_SPEED_HS};
    }

    cross_reset_state_speed: cross cp_reset_from_state, cp_speed_rst;
  endgroup

  // ---------------------------------------------------------------------------
  // B4: speed selection
  // ---------------------------------------------------------------------------
  covergroup usb_speed_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = {"usb_speed_", DEV_NAME};

    cp_speed: coverpoint speed iff (rst_n) {
      bins full_speed = {LINK_SPEED_FS};
      bins high_speed = {LINK_SPEED_HS};
      // The reserved encodings should never be reported by a running link.
      bins illegal_reserved = {LINK_SPEED_RESERVED, LINK_SPEED_SS};
    }

    cp_force_fs: coverpoint force_fs iff (rst_n);

    // The UTMI selects are how the speed is actually realised on the PHY.
    // Covering them separately catches a link that reports one speed while
    // the transceiver is configured for the other.
    cp_xcvrselect: coverpoint utmi_xcvrselect iff (rst_n);
    cp_termselect: coverpoint utmi_termselect iff (rst_n);

    // The point of the force-FS control: did asserting it actually yield a
    // full-speed link. The force_fs=1 x high_speed bin should stay empty.
    cross_force_fs_speed: cross cp_force_fs, cp_speed;

    // Ties the reported speed to the transceiver configuration that produced
    // it, so a disagreement is visible as an unexpected bin.
    cross_speed_xcvr: cross cp_speed, cp_xcvrselect, cp_termselect;
  endgroup

  usb_enum_cg    usb_enum_cg_inst    = new();
  usb_connect_cg usb_connect_cg_inst = new();
  usb_reset_cg   usb_reset_cg_inst   = new();
  usb_speed_cg   usb_speed_cg_inst   = new();

endmodule : usb_dev_enum_cov

// File contains AI-generated response based on internal company sources
