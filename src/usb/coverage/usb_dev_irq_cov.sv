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
// AREA D2: interrupt registers, per source.
//
// Plain SystemVerilog passive observer: inputs only, no UVM, no classes, no
// DPI. One instance per device, fed by the bench probe with the usb_reg_if
// interrupt register slices.
//
// WHY THIS IS SEPARATE FROM usb_interrupt_cg
// ------------------------------------------
// usb_interrupt_cg in usb_dev_ep_cov measures the OUTPUT PINS: did IRQ or FIQ
// toggle, and in which link state. That answers "was an interrupt delivered"
// but not "which source raised it", "was it enabled", or "did the write-1-to-
// clear actually clear it". Those are register-level questions and they need
// the register-level state, which is what this observer takes.
//
// REGISTER MODEL
// --------------
// usb_reg_if does not hold INTSTAT as one word. It keeps three slices, and
// assembles the readback:
//
//   reg_ep_int_status(C_NBPHYSEP+1 downto 0)  -> INTSTAT[C_NBPHYSEP+1:0]
//   reg_frame_int_status                      -> INTSTAT[30]
//   reg_dev_int_status                        -> INTSTAT[31]
//
// INTEN (word 9) and INTROUTE (word 11) share that bit layout. The pin logic
// in proc_hw_int_generation is a flat OR over all sources of
// (status AND enable), steered per source by the route bit:
//
//   route = 0 -> contributes to IRQ
//   route = 1 -> contributes to FIQ
//
// so a source only reaches a pin when it is both pending AND enabled, and the
// cross of those two is the property worth covering. A pending-but-masked
// source that still drove a pin, or an enabled-and-pending source that did
// not, are both real bugs and both invisible to pin-only coverage.
//
// EP INDEXING
// -----------
// The endpoint status slice is indexed by PHYSICAL endpoint number, which is
// 2*logical + direction, so physical 0 and 1 are EP0 OUT and EP0 IN. Bins are
// kept per physical index because that is the number the DMA uses when it sets
// the bit (dma_physepnr), and collapsing to logical would hide a direction
// mix-up.
//
// QUESTIONS ANSWERED
// ------------------
//   - Which interrupt sources were ever raised, per device?
//   - Was each source seen both enabled and masked while pending?
//   - Was each source routed to IRQ and to FIQ?
//   - Did firmware exercise write-1-to-clear, and force-set via INTSETSTAT?
//   - Was a source re-raised while already pending, and cleared while another
//     source was still pending?
//   - Did more than one source ever sit pending at the same time?
module usb_dev_irq_cov
  import usb_cov_pkg::*;
#(
  parameter string       DEV_NAME = "dev0",
  // Number of physical endpoint status bits, matching the width of the
  // reg_ep_int_status slice: C_NBPHYSEP+2 bits for C_NBPHYSEP+1 downto 0.
  parameter int unsigned NUM_PHYS_EP = 16
) (
  input logic clk,
  input logic rst_n,

  // ---------------------------------------------------------------------------
  // Interrupt register slices (usb_reg_if_N)
  // ---------------------------------------------------------------------------
  // Status: set by hardware on the event, cleared by a write of 1 to INTSTAT.
  input logic [NUM_PHYS_EP-1:0] ep_int_status,
  input logic                   frame_int_status,
  input logic                   dev_int_status,

  // Enable: gates the contribution of each source to its pin.
  input logic [NUM_PHYS_EP-1:0] ep_int_enable,
  input logic                   frame_int_enable,
  input logic                   dev_int_enable,

  // Route: 0 sends the source to IRQ, 1 to FIQ.
  input logic [NUM_PHYS_EP-1:0] ep_int_route,
  input logic                   frame_int_route,
  input logic                   dev_int_route,

  // ---------------------------------------------------------------------------
  // Register write strobes, decoded by the probe from the CSR word address
  // ---------------------------------------------------------------------------
  // One strobe per interrupt register, asserted for the cycle the write takes
  // effect. These are what make the clear and force-set paths observable: the
  // status bits alone cannot distinguish "cleared by firmware" from "never
  // set".
  input logic        wr_intstat,     // word 8:  write 1 clears
  input logic        wr_inten,       // word 9
  input logic        wr_intsetstat,  // word 10: write 1 sets
  input logic        wr_introute,    // word 11
  input logic [31:0] wr_data,

  // Interrupt pins, to confirm the enable/route logic actually drove them.
  input logic usb_irq,
  input logic usb_fiq,

  // Link state, to separate a wakeup interrupt from ordinary traffic.
  input logic dcon,
  input logic dsus,
  input logic lpm_sus
);

  // ---------------------------------------------------------------------------
  // Flattened source view
  // ---------------------------------------------------------------------------
  // The three slices are concatenated into one vector per register so the
  // per-source loops below can treat every source identically. Index
  // [NUM_PHYS_EP] is the frame source and [NUM_PHYS_EP+1] the device source,
  // mirroring INTSTAT[30] and INTSTAT[31].
  localparam int unsigned NUM_SRC   = NUM_PHYS_EP + 2;
  localparam int unsigned IDX_FRAME = NUM_PHYS_EP;
  localparam int unsigned IDX_DEV   = NUM_PHYS_EP + 1;

  logic [NUM_SRC-1:0] src_status;
  logic [NUM_SRC-1:0] src_enable;
  logic [NUM_SRC-1:0] src_route;

  always_comb begin
    src_status = {dev_int_status, frame_int_status, ep_int_status};
    src_enable = {dev_int_enable, frame_int_enable, ep_int_enable};
    src_route  = {dev_int_route,  frame_int_route,  ep_int_route};
  end

  // Previous status, to detect the set and clear edges per source.
  logic [NUM_SRC-1:0] src_status_q;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) src_status_q <= '0;
    else        src_status_q <= src_status;
  end

  // ---------------------------------------------------------------------------
  // Event classification
  // ---------------------------------------------------------------------------
  // The sampled source index. A covergroup samples one scalar, so the observer
  // picks the lowest-numbered source that changed this cycle and records it;
  // the pending-count coverpoint below is what catches the simultaneous case.
  int unsigned        set_idx;
  int unsigned        clr_idx;
  logic               any_set;
  logic               any_clr;
  int_src_class_e     set_class;
  int_src_class_e     clr_class;
  logic               set_enabled;
  int_dest_e          set_dest;

  // Number of sources pending right now, and whether another source was still
  // pending when one was cleared.
  int unsigned        pending_n;
  int_pending_count_e pending_class;
  logic               clr_with_others_pending;

  always_comb begin

    any_set = 1'b0;
    any_clr = 1'b0;
    set_idx = 0;
    clr_idx = 0;

    for (int unsigned i = 0; i < NUM_SRC; i++) begin
      if (src_status[i] && !src_status_q[i] && !any_set) begin
        any_set = 1'b1;
        set_idx = i;
      end
      if (!src_status[i] && src_status_q[i] && !any_clr) begin
        any_clr = 1'b1;
        clr_idx = i;
      end
    end

    set_class = (set_idx == IDX_DEV)   ? INT_SRC_DEV   :
                (set_idx == IDX_FRAME) ? INT_SRC_FRAME : INT_SRC_EP;
    clr_class = (clr_idx == IDX_DEV)   ? INT_SRC_DEV   :
                (clr_idx == IDX_FRAME) ? INT_SRC_FRAME : INT_SRC_EP;

    set_enabled = src_enable[set_idx];
    set_dest    = int_dest(src_route[set_idx]);

    pending_n = 0;
    for (int unsigned i = 0; i < NUM_SRC; i++) begin
      if (src_status[i]) pending_n++;
    end
    pending_class = int_pending_count(pending_n);

    // At a clear edge the cleared bit is already low in src_status, so a
    // non-zero count means some other source is still waiting.
    clr_with_others_pending = any_clr && (pending_n > 0);
  end


  // Which register was written this cycle. Only one strobe can be active at a
  // time because they are decoded from the same word address.
  int_write_kind_e write_kind;

  always_comb begin
    if      (wr_intstat)    write_kind = INT_WR_CLEAR;
    else if (wr_intsetstat) write_kind = INT_WR_FORCE_SET;
    else if (wr_inten)      write_kind = INT_WR_ENABLE;
    else if (wr_introute)   write_kind = INT_WR_ROUTE;
    else                    write_kind = INT_WR_NONE;
  end

  logic any_write;
  always_comb any_write = (write_kind != INT_WR_NONE);

  link_state_e state;
  always_comb state = link_state(dcon, dsus, lpm_sus);

  // A source that is pending and enabled must be driving a pin. Tracked as a
  // coverpoint rather than an assertion so the observer stays passive.
  logic any_pending_enabled;
  always_comb any_pending_enabled = |(src_status & src_enable);

  // ---------------------------------------------------------------------------
  // D2a: interrupt source identity
  // ---------------------------------------------------------------------------
  covergroup usb_irq_source_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = {"usb_irq_source_", DEV_NAME};

    // Which class of source fired. The device and frame sources are single
    // bits; the endpoint class covers the whole status slice.
    cp_set_class: coverpoint set_class iff (rst_n && any_set);

    // The physical endpoint index that raised the interrupt. Per index rather
    // than collapsed, because physical index is 2*logical+dir and a direction
    // mix-up is exactly the bug this separates out.
    cp_set_ep: coverpoint set_idx iff (rst_n && any_set && (set_class == INT_SRC_EP)) {
      bins physep[] = {[0:15]};
    }

    // Was the source enabled at the moment it became pending? Both answers
    // are legal and both must be seen: masked-pending is the path where the
    // status bit latches but no pin moves.
    cp_set_enabled: coverpoint set_enabled iff (rst_n && any_set) {
      bins masked  = {1'b0};
      bins enabled = {1'b1};
    }

    // Where INTROUTE was pointing this source. FIQ is the leg that the pin
    // coverage shows as never exercised.
    cp_set_dest: coverpoint set_dest iff (rst_n && any_set);

    // Clearing is its own event: a source that sets but never clears is a
    // stuck interrupt.
    cp_clr_class: coverpoint clr_class iff (rst_n && any_clr);

    // The functional matrix: every source class, seen both enabled and
    // masked, routed to both pins.
    cross_class_enabled: cross cp_set_class, cp_set_enabled;
    cross_class_dest:    cross cp_set_class, cp_set_dest;
    cross_enabled_dest:  cross cp_set_enabled, cp_set_dest;
  endgroup

  // ---------------------------------------------------------------------------
  // D2b: interrupt register accesses
  // ---------------------------------------------------------------------------
  covergroup usb_irq_regaccess_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = {"usb_irq_regaccess_", DEV_NAME};

    // Which of the four interrupt registers firmware actually touched. A test
    // suite that never writes INTROUTE leaves the FIQ leg unconfigured, which
    // is the current state of this regression.
    cp_write_kind: coverpoint write_kind iff (rst_n && any_write);

    // Write-1-to-clear is only exercised if a write actually carried set bits;
    // a write of zero is a no-op and must not be counted as a clear.
    cp_clear_nonzero: coverpoint (|wr_data) iff (rst_n && wr_intstat) {
      bins no_bits_set   = {1'b0};
      bins some_bits_set = {1'b1};
    }

    // INTSTAT and INTSETSTAT share a bit layout and differ only in address.
    // Both must be seen or the force-set path is untested.
    cp_setstat_nonzero: coverpoint (|wr_data) iff (rst_n && wr_intsetstat) {
      bins no_bits_set   = {1'b0};
      bins some_bits_set = {1'b1};
    }

    // Register writes while suspended are the firmware-serviced wakeup path.
    cp_write_state: coverpoint state iff (rst_n && any_write);

    cross_kind_state: cross cp_write_kind, cp_write_state;
  endgroup

  // ---------------------------------------------------------------------------
  // D2c: interrupt concurrency and pin consistency
  // ---------------------------------------------------------------------------
  covergroup usb_irq_concurrency_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = {"usb_irq_concurrency_", DEV_NAME};

    // More than one source pending at once. The pin is a flat OR, so this is
    // where a clear-one-but-not-the-other bug shows up.
    cp_pending: coverpoint pending_class iff (rst_n);

    // A clear that happened while another source was still pending must leave
    // the pin asserted.
    cp_clr_with_others: coverpoint clr_with_others_pending iff (rst_n && any_clr) {
      bins last_source      = {1'b0};
      bins others_remaining = {1'b1};
    }

    // Pin state against the aggregate pending-and-enabled condition. Seeing
    // both asserted together and both idle together is the consistency
    // evidence; the mismatch combinations are where a gating bug lands.
    cp_pending_enabled: coverpoint any_pending_enabled iff (rst_n);
    cp_pin_irq:         coverpoint usb_irq             iff (rst_n);
    cp_pin_fiq:         coverpoint usb_fiq             iff (rst_n);

    cross_pending_irq: cross cp_pending_enabled, cp_pin_irq;
    cross_pending_fiq: cross cp_pending_enabled, cp_pin_fiq;

    // Both pins active at once: legal when two sources are routed differently,
    // and only reachable if INTROUTE was actually programmed.
    cross_irq_fiq: cross cp_pin_irq, cp_pin_fiq;
  endgroup

  usb_irq_source_cg      usb_irq_source_cg_inst      = new();
  usb_irq_regaccess_cg   usb_irq_regaccess_cg_inst   = new();
  usb_irq_concurrency_cg usb_irq_concurrency_cg_inst = new();

endmodule : usb_dev_irq_cov

// File contains AI-generated response based on internal company sources
