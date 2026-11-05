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
// AREA F - compound device multiplexing and cross-function concurrency.
//
// WHY THESE TWO GROUPS ARE TOGETHER
// ---------------------------------
// Both answer questions that only exist because this is a COMPOUND device:
// one serial engine and one DMA are time-multiplexed across hub + dev0 + dev1,
// and the two software devices have independent link state machines. Neither
// question is answerable from a single device's own registers, so neither
// belongs in the per-device observers of areas A-D.
//
// ATTACHMENT
// ----------
// Probe-fed. Every input is supplied by a bench-specific probe module (see
// src/integration/testbench/usb_cov_probe_caliptra_ss.sv) because the sources
// are ports of VHDL sub-instances inside the compound, which a SystemVerilog
// bind cannot reach. The covergroup and bin names contain no hierarchy, so a
// usb_top_tb probe driving the same port list produces a mergeable database.
//
// QUESTIONS ANSWERED
// ------------------
//   - Was the serial engine ever actually handed to each of the three
//     functions, and did it interleave between them rather than serving one
//     function for the whole run?
//   - Did the DMA context follow the selection into the hardware-device range
//     as well as the software-device range?
//   - Which device-enable patterns were ever live at once, and under which
//     hub/bypass topology?
//   - Were dev0 and dev1 ever in DIFFERENT link power states at the same time?
//     That is the case a single-device bench cannot produce at all, and it is
//     exactly what the dual_device_* tests are for.
//
// NOT COVERED HERE
// ----------------
// Per-device link state detail (area A), per-device transfers (area C) and
// hub-port state (area E). This file samples only the relationship BETWEEN
// functions.
module usb_compound_cov
  import usb_cov_pkg::*;
#(
  // Number of hardware (hub) functions ahead of the software devices in the
  // pie_dev_selected numbering. Selection values below this are the hub.
  parameter int unsigned NUM_HW_DEVICES = 1
) (
  input logic       clk,
  input logic       rst_n,

  // ---- Function selection and DMA context ----
  input logic [1:0] pie_dev_selected,
  input logic       dma_ahb_selected,

  // ---- Device-enable legs, one per logical function ----
  input logic       deviceenabled_hub,
  input logic       deviceenabled_dev0,
  input logic       deviceenabled_dev1,

  // ---- Topology strap ----
  input logic       hub_enable,

  // ---- Per-device link state terms, used only for the concurrency cross ----
  input logic       dev0_dcon,
  input logic       dev0_dsus,
  input logic       dev0_lpm_sus,
  input logic [6:0] dev0_addr,
  input logic       dev1_dcon,
  input logic       dev1_dsus,
  input logic       dev1_lpm_sus,
  input logic [6:0] dev1_addr
);

  // ---------------------------------------------------------------------------
  // Derived observation state
  // ---------------------------------------------------------------------------
  // Which logical function the serial engine is currently serving. One engine
  // and one DMA are shared by all three functions, so this selector is the
  // compound device's defining mechanism.
  usb_function_e selected_function;
  always_comb begin
    if (pie_dev_selected < NUM_HW_DEVICES) begin
      selected_function = USB_FUNC_HUB;
    end else if (pie_dev_selected == NUM_HW_DEVICES) begin
      selected_function = USB_FUNC_DEV0;
    end else begin
      selected_function = USB_FUNC_DEV1;
    end
  end

  // Link state per software device, decoded identically to area A so the bin
  // names mean the same thing in both places. The cross of the two is the only
  // coverage that proves the two state machines are genuinely independent.
  link_state_e dev0_state;
  link_state_e dev1_state;
  always_comb dev0_state = link_state(dev0_dcon, dev0_dsus, dev0_lpm_sus);
  always_comb dev1_state = link_state(dev1_dcon, dev1_dsus, dev1_lpm_sus);

  // A non-zero device address is the observable end of enumeration: the host
  // has issued SET_ADDRESS and the device accepted it. Both non-zero at once
  // means the host really did enumerate two functions behind the hub.
  logic dev0_enumerated;
  logic dev1_enumerated;
  always_comb dev0_enumerated = (dev0_addr != 7'd0);
  always_comb dev1_enumerated = (dev1_addr != 7'd0);

  // ---------------------------------------------------------------------------
  // F1 - function multiplexing
  // ---------------------------------------------------------------------------
  covergroup usb_compound_function_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = "usb_compound_function";

    // Was each function ever selected at all. A function that is never
    // selected has had none of its transfer coverage exercised, which makes
    // the corresponding area C numbers meaningless rather than merely low.
    cp_function: coverpoint selected_function iff (rst_n);

    // The DMA context must follow the selection. Crossing the two shows the
    // hardware-device and software-device DMA paths were both taken.
    cp_dma_context: coverpoint dma_ahb_selected iff (rst_n) {
      bins hw_device_context = {1'b1};
      bins sw_device_context = {1'b0};
    }
    cross_function_dma: cross cp_function, cp_dma_context;

    // Interleaving, not just presence. Serving one function for the whole run
    // and then the next is a different test than alternating between them,
    // and only the second exercises the context switch.
    cp_function_interleave: coverpoint selected_function iff (rst_n) {
      bins hub_to_dev0  = (USB_FUNC_HUB  => USB_FUNC_DEV0);
      bins hub_to_dev1  = (USB_FUNC_HUB  => USB_FUNC_DEV1);
      bins dev0_to_hub  = (USB_FUNC_DEV0 => USB_FUNC_HUB);
      bins dev1_to_hub  = (USB_FUNC_DEV1 => USB_FUNC_HUB);
      bins dev0_to_dev1 = (USB_FUNC_DEV0 => USB_FUNC_DEV1);
      bins dev1_to_dev0 = (USB_FUNC_DEV1 => USB_FUNC_DEV0);
    }

    // Which enable patterns were ever live together.
    cp_enabled_legs: coverpoint {deviceenabled_dev1, deviceenabled_dev0, deviceenabled_hub}
                     iff (rst_n) {
      bins none          = {3'b000};
      bins hub_only      = {3'b001};
      bins dev0_only     = {3'b010};
      bins hub_dev0      = {3'b011};
      bins dev1_only     = {3'b100};
      bins hub_dev1      = {3'b101};
      bins dev0_dev1     = {3'b110};
      bins hub_dev0_dev1 = {3'b111};
    }

    // The hub strap changes which enable patterns are even reachable, so the
    // cross records which topology produced which enable pattern.
    cp_hub_enable: coverpoint hub_enable iff (rst_n);
    cross_mode_enabled_legs: cross cp_hub_enable, cp_enabled_legs;
  endgroup

  // ---------------------------------------------------------------------------
  // F2 - cross-function concurrency
  // ---------------------------------------------------------------------------
  // The headline measurement of the compound device. Per-device instancing of
  // area A gives each device's own state history, but only this cross answers
  // "were they ever in different states at the same time", which is what
  // proves the two link state machines do not share state by accident.
  covergroup usb_compound_concurrency_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = "usb_compound_concurrency";

    cp_dev0_state: coverpoint dev0_state iff (rst_n);
    cp_dev1_state: coverpoint dev1_state iff (rst_n);

    // Full product on purpose. The diagonal entries are the uninteresting
    // "both doing the same thing" cases and the off-diagonal entries are the
    // whole point, so suppressing either half would hide the comparison.
    cross_dev_states: cross cp_dev0_state, cp_dev1_state;

    // Did the host ever hold addresses for both functions at once. Without
    // this, two devices each enumerated at different times reads the same as
    // two devices enumerated together.
    cp_both_enumerated: coverpoint {dev1_enumerated, dev0_enumerated} iff (rst_n) {
      bins neither   = {2'b00};
      bins dev0_only = {2'b01};
      bins dev1_only = {2'b10};
      bins both      = {2'b11};
    }
  endgroup

  usb_compound_function_cg    usb_compound_function_cg_inst    = new();
  usb_compound_concurrency_cg usb_compound_concurrency_cg_inst = new();

endmodule : usb_compound_cov

// File contains AI-generated response based on internal company sources
