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
// AREAS C and D: endpoint / transfer activity and interrupt delivery.
//
// Plain SystemVerilog passive observer: inputs only, no UVM, no classes, no
// DPI. One instance per device, fed by the bench probe.
//
// THE DEVICE QUALIFIER IS LOAD BEARING
// ------------------------------------
// The transaction-layer signals come from usb_pie, which is instantiated
// EXACTLY ONCE in the compound and time-multiplexed across the hub and the
// two software devices. Every PIE-sourced coverpoint is therefore qualified
// with xfer_for_me, which combines:
//
//   pie_dev_selected == MY_SEL   the PIE is currently serving this device
//   xfer_active                  a token has been decoded and the
//                                transaction has not ended yet
//
// Without the first term, dev1 traffic would be recorded against dev0.
// Without the second, the idle selection value (0) would be mis-counted as
// hub traffic on every idle cycle.
//
// pie_dev_selected is safe to use live: it is driven from a registered
// signal that usb_pie assigns only at token decode (the new_inoutsetup_vld
// branch, from the matched device address), so it holds for the whole
// transaction and changes only when the next token selects someone else.
//
// QUESTIONS ANSWERED
// ------------------
//   - Which endpoints saw traffic, in which direction, of which kind?
//   - Did every endpoint reach a successful transfer, and which error and
//     flow-control classes were produced?
//   - Were the packet-size boundary cases exercised: zero length, and the
//     architectural max-packet limits?
//   - Was double buffering actually used, and did the data toggle track it?
//   - Were interrupts delivered, and were any raised while suspended?
module usb_dev_ep_cov
  import usb_cov_pkg::*;
#(
  parameter string       DEV_NAME = "dev0",
  // Index this instance watches, matching pie_dev_selected and
  // usbreg_deviceenabled numbering (hub = 0, dev0 = 1, dev1 = 2).
  parameter int unsigned MY_SEL   = USB_SEL_DEV0
) (
  input logic        clk,
  input logic        rst_n,

  // ---------------------------------------------------------------------------
  // Shared PIE transaction layer (usb_pie_1)
  // ---------------------------------------------------------------------------
  input logic [1:0]  pie_dev_selected,  // which function the PIE is serving
  input logic        epinfo_req,        // token decoded, transaction starting
  input logic        endtransfer,       // transaction complete

  input logic [3:0]  ep_num,            // pie_epinfo_epnr
  input logic        ep_dir,            // pie_epinfo_epdir, 1 = IN
  input logic        ep_iso,            // epinfo_iso
  input logic        ep_stall,          // epinfo_stall
  input logic        ep_disabled,       // epinfo_disabled
  input logic        ep_active,         // epinfo_active
  input logic        ep_toggle,         // epinfo_toggle

  input logic [14:0] ep_nbytes,         // epinfo_nbytes, requested length

  input logic        xfer_success,      // pie_success
  input logic        xfer_error,        // pie_error
  input logic [3:0]  xfer_errortype,    // pie_errortype
  input logic        xfer_sent_nak,     // pie_sentNAK

  // ---------------------------------------------------------------------------
  // Per-device register state (usb_reg_if_N)
  // ---------------------------------------------------------------------------
  input logic        ep_bufinuse_any,   // any bit of usbreg_ep_bufinuse
  input logic        ep_skip_any,       // any bit of usbreg_ep_skip

  // Interrupt outputs and the link state to qualify them.
  input logic        usb_irq,           // USB_Int_Req_Irq
  input logic        dcon,
  input logic        dsus,
  input logic        lpm_sus
);

  // ---------------------------------------------------------------------------
  // Transaction attribution window
  // ---------------------------------------------------------------------------
  // Held between token decode and end of transfer so the PIE selection can
  // only be credited to this device while a transaction of its own is in
  // flight.
  logic xfer_active;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)           xfer_active <= 1'b0;
    else if (epinfo_req)  xfer_active <= 1'b1;
    else if (endtransfer) xfer_active <= 1'b0;
  end

  logic xfer_for_me;
  always_comb xfer_for_me = rst_n &&
                            (pie_dev_selected == MY_SEL[1:0]) &&
                            (xfer_active || epinfo_req);

  // The end-of-transfer strobe is where the outcome and the final byte count
  // are valid, so the outcome groups sample there rather than continuously.
  logic xfer_done_for_me;
  always_comb xfer_done_for_me = xfer_for_me && endtransfer;

  // ---------------------------------------------------------------------------
  // Derived classifications
  // ---------------------------------------------------------------------------
  ep_kind_e         kind;
  ep_dir_e          dir;
  xfer_outcome_e    outcome;
  xfer_size_class_e size_class;
  link_state_e      state;

  always_comb begin
    kind       = ep_kind(ep_num, ep_iso);
    dir        = ep_dir ? EP_DIR_IN : EP_DIR_OUT;
    outcome    = xfer_outcome(xfer_success, xfer_error, xfer_sent_nak);
    size_class = xfer_size_class(ep_nbytes);
    state      = link_state(dcon, dsus, lpm_sus);
  end

  // ---------------------------------------------------------------------------
  // C1: endpoint activity
  // ---------------------------------------------------------------------------
  covergroup usb_ep_activity_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = {"usb_ep_activity_", DEV_NAME};

    // Endpoint number as presented by the decoded token. Binned individually
    // because "some endpoint was used" does not answer whether the endpoint
    // the test was written for was reached.
    cp_ep_num: coverpoint ep_num iff (xfer_for_me) {
      bins ep[] = {[0:15]};
    }

    cp_dir: coverpoint dir iff (xfer_for_me);

    cp_ep_kind: coverpoint kind iff (xfer_for_me);

    // An endpoint is only half covered if only one direction was used; the
    // loopback tests depend on both.
    cross_ep_dir:   cross cp_ep_num, cp_dir;
    cross_kind_dir: cross cp_ep_kind, cp_dir;
  endgroup

  // ---------------------------------------------------------------------------
  // C2: transfer outcome
  // ---------------------------------------------------------------------------
  covergroup usb_transfer_outcome_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = {"usb_transfer_outcome_", DEV_NAME};

    cp_outcome: coverpoint outcome iff (xfer_done_for_me);

    // The IP's own error taxonomy rather than a single "an error happened"
    // bit, so a CRC failure is distinguishable from a timeout or an overrun.
    //
    // Only the codes the PIE can actually drive are binned. The encoding is
    // the SetError procedure of usb_pie.m.vhdl (kept there as a comment at
    // lines 1901-1918 after a lint fix inlined it); the live assignments in
    // that file are the authority for which codes the design still produces.
    //
    // Deliberately NOT binned, because no reachable stimulus can hit them and
    // an unhittable bin only depresses the score:
    //
    //   0x0 NO_ERROR    this coverpoint is qualified on xfer_error, so the
    //                   "no error" code cannot coincide with a sample
    //   0x7 BABBLE      no live assignment, the procedure arm is commented out
    //   0xC EMPTYPACK   no live assignment
    //   0xD BITSTUFF    no live assignment
    //   0xE SYNC        no live assignment
    //
    // 0xD and 0xE matter for test writing: a wire-level bit-stuffing or SYNC
    // corruption is never reported through this field, so injecting one is
    // not a way to close this coverpoint.
    cp_errortype: coverpoint xfer_errortype iff (xfer_done_for_me && xfer_error) {
      bins pid_encoding      = {4'h1};
      bins pid_unknown       = {4'h2};
      bins packet_unexpected = {4'h3};
      bins token_crc         = {4'h4};
      bins data_crc          = {4'h5};
      bins timeout           = {4'h6};
      bins tr_eop            = {4'h8};
      bins sent_received_nak = {4'h9};
      bins sent_stall        = {4'hA};
      bins overrun           = {4'hB};
      bins wrong_data_toggle = {4'hF};
    }

    // STALL is the endpoint halting itself, which is a protocol response
    // rather than a transfer error; the halt tests target it specifically.
    cp_stall: coverpoint ep_stall iff (xfer_for_me) {
      bins not_stalled = {1'b0};
      bins stalled     = {1'b1};
    }

    cp_ep_num_out: coverpoint ep_num iff (xfer_done_for_me) {
      bins ep[] = {[0:15]};
    }

    cp_kind_out: coverpoint kind iff (xfer_done_for_me);

    // Per-endpoint outcome is the useful form: one endpoint erroring while
    // the others succeed is exactly what a flow-control bug looks like.
    cross_outcome_ep:    cross cp_outcome, cp_ep_num_out;
    cross_errtype_kind:  cross cp_errortype, cp_kind_out;
  endgroup

  // ---------------------------------------------------------------------------
  // C3: transfer size
  // ---------------------------------------------------------------------------
  covergroup usb_transfer_size_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = {"usb_transfer_size_", DEV_NAME};

    // Bucketed at the architectural packet boundaries; see xfer_size_class
    // in usb_cov_pkg for why an exact per-endpoint max packet cannot be
    // reconstructed from observable signals.
    cp_size: coverpoint size_class iff (xfer_done_for_me);

    cp_kind_sz: coverpoint kind iff (xfer_done_for_me);
    cp_dir_sz:  coverpoint dir  iff (xfer_done_for_me);

    // Which limit applies depends on the endpoint kind, so the cross is what
    // makes a boundary hit interpretable.
    cross_size_kind: cross cp_size, cp_kind_sz;
    cross_size_dir:  cross cp_size, cp_dir_sz;
  endgroup

  // ---------------------------------------------------------------------------
  // C4: endpoint buffering
  // ---------------------------------------------------------------------------
  covergroup usb_ep_buffer_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = {"usb_ep_buffer_", DEV_NAME};

    // The data toggle must alternate across successive transfers on an
    // endpoint; both values must be seen for the sequencing to be exercised.
    cp_toggle: coverpoint ep_toggle iff (xfer_for_me);

    cp_bufinuse: coverpoint ep_bufinuse_any iff (rst_n);

    // EPSKIP is the abort path, used by the disconnect and error tests.
    cp_skip: coverpoint ep_skip_any iff (rst_n) {
      bins skip_requested = (1'b0 => 1'b1);
    }

    // A disabled or inactive endpoint being addressed is the unsupported
    // endpoint scenario, which must produce a stall rather than a hang.
    cp_disabled: coverpoint ep_disabled iff (xfer_for_me);
    cp_inactive: coverpoint ep_active   iff (xfer_for_me) {
      bins active   = {1'b1};
      bins inactive = {1'b0};
    }

    // Double buffering is only proven if the toggle advanced while a second
    // buffer was in use.
    cross_toggle_bufinuse: cross cp_toggle, cp_bufinuse;
  endgroup

  // ---------------------------------------------------------------------------
  // D1: interrupt delivery
  // ---------------------------------------------------------------------------
  covergroup usb_interrupt_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = {"usb_interrupt_", DEV_NAME};

    // Both edges: an interrupt that asserts and never clears is a different
    // and worse bug than one that never asserts.
    cp_irq: coverpoint usb_irq iff (rst_n) {
      bins assert_edge   = (1'b0 => 1'b1);
      bins deassert_edge = (1'b1 => 1'b0);
    }

    cp_state: coverpoint state iff (rst_n);

    // An interrupt raised while the link is suspended is the wakeup path;
    // one raised while active is ordinary traffic. The cross separates them.
    cross_irq_state: cross cp_irq, cp_state;
  endgroup

  usb_ep_activity_cg       usb_ep_activity_cg_inst       = new();
  usb_transfer_outcome_cg  usb_transfer_outcome_cg_inst  = new();
  usb_transfer_size_cg     usb_transfer_size_cg_inst     = new();
  usb_ep_buffer_cg         usb_ep_buffer_cg_inst         = new();
  usb_interrupt_cg         usb_interrupt_cg_inst         = new();

endmodule : usb_dev_ep_cov

// File contains AI-generated response based on internal company sources
