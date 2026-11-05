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
// AREA: USB address space and access semantics.
//
// Every covergroup that answers an address-map or access-semantics question
// lives in this one module, so the whole area can be reviewed, enabled or
// excluded as a unit.
//
// Plain SystemVerilog passive observer: inputs only, no UVM, no classes, no
// DPI. It is attached with bind, so no design file is modified.
//
// ATTACHMENT
// ----------
// Bound by MODULE TYPE to usb_compound_ahb_decoder (see usb_cov_bind.sv).
// A bind resolves its port expressions in the TARGET module's own scope, so
// there is no hierarchy path in this file and none in the bind statement
// either. That is what makes this area mergeable: the decoder is the same
// SystemVerilog module in the subsystem bench (caliptra_ss_top_tb) and in the
// compound unit bench (usb_top_tb), so both produce identical covergroup and
// bin names and URG merges the two databases with no manual mapping.
//
// The decoder is also the right observation point on its own merits: it is
// the single place where the address, the shape qualification and the chosen
// responder all exist at the same time.
//
// QUESTIONS ANSWERED
// ------------------
//   - Was every architecturally distinct combo sub-region accessed, in both
//     directions?
//   - Did each region return its ARCHITECTED response class: the decode hole
//     an ERROR, the hub aperture padding an OKAY?
//   - Were non-32-bit and unaligned accesses actually attempted, and did they
//     select no responder?
//   - Within the hub bank, was each functionally distinct word class touched?
//
// NOT COVERED HERE
// ----------------
// Individual addresses, data values, and the decoder FSM as such. The
// registered responder state is sampled only to distinguish the two-phase
// error sequence, which is architected behaviour and cannot be inferred from
// the region decode alone.
module usb_addr_cov
  import usb_cov_pkg::*;
#(
  // Mirrors the decoder's own C_HUB_FIFO_SIZE and the power-of-two aperture it
  // derives from it, so the implemented hub words and the aperture padding can
  // be told apart without re-deriving the geometry here. The bind passes the
  // target's own parameter, so these defaults are never relied upon.
  parameter int unsigned HUB_WORDS          = 196,
  parameter int unsigned HUB_APERTURE_BYTES = 1024
) (
  input logic        clk,
  input logic        rst_n,

  // Address phase, qualified exactly as the decoder qualifies it.
  input logic        addr_phase_active,
  input logic [31:0] addr_phase_byte_addr,
  input logic [2:0]  hsize,
  input logic [1:0]  haddr_low,
  input logic        hwrite,
  input logic        hready,

  // Downstream selects, used to prove an unqualified access selected nothing.
  input logic        dev0_csr_hsel,
  input logic        hub_hsel,
  input logic        recovery_hsel,
  input logic [31:0] hub_word_addr,

  // Data phase as returned upstream.
  input logic [1:0]  hresp,
  input logic        hreadyout,
  input logic        error_first_phase,
  input logic        error_final_phase
);

  // ---------------------------------------------------------------------------
  // Address-phase observation state
  // ---------------------------------------------------------------------------
  // An address phase is only meaningful to coverage when it is ACCEPTED: the
  // manager must be presenting an active transfer and the global HREADY must
  // let it through. Sampling on anything else would attribute a region to a
  // transfer that never happened and inflate the coverage.
  logic          access_accepted;
  combo_region_e sampled_region;
  access_dir_e   sampled_dir;
  access_shape_e sampled_shape;
  logic          any_select;

  always_comb begin
    access_accepted = addr_phase_active && hready;
    sampled_region  = combo_region(addr_phase_byte_addr, HUB_WORDS, HUB_APERTURE_BYTES);
    sampled_dir     = hwrite ? ACCESS_WRITE : ACCESS_READ;
    sampled_shape   = access_shape(hsize, haddr_low);
    any_select      = dev0_csr_hsel || hub_hsel || recovery_hsel;
  end

  // ---------------------------------------------------------------------------
  // Data-phase context
  // ---------------------------------------------------------------------------
  // The response is owned by the registered responder in the data phase, so
  // the region and direction captured at the matching address phase have to be
  // registered to be available when the response appears. Re-decoding live
  // would read the NEXT transfer's address.
  combo_region_e data_phase_region;
  access_dir_e   data_phase_dir;
  logic          data_phase_valid;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data_phase_region <= COMBO_REGION_DEV0_CSR;
      data_phase_dir    <= ACCESS_READ;
      data_phase_valid  <= 1'b0;
    end else if (error_first_phase) begin
      // The first error phase drives HREADYOUT low and advances on its own, so
      // the captured region must survive into the final phase.
      data_phase_valid <= 1'b1;
    end else if (hready) begin
      data_phase_region <= sampled_region;
      data_phase_dir    <= sampled_dir;
      data_phase_valid  <= access_accepted;
    end
  end

  // ---------------------------------------------------------------------------
  // G1 - the whole address-map and access-semantics contract in one group
  // ---------------------------------------------------------------------------
  // Previously three groups (access / response / error phase). They are merged
  // because they describe ONE transfer seen at successive points in time, and
  // splitting them put the halves of the contract in different reports. Each
  // coverpoint keeps its own iff qualifier, so the address-phase and the
  // data-phase samples remain correctly gated; the cp_resp_* coverpoints are
  // named apart from the address-phase cp_region/cp_dir precisely so that a
  // cross can never accidentally pair an address-phase term with a data-phase
  // one, which would compare two different transfers.
  covergroup usb_combo_access_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = "usb_combo_access";

    cp_region: coverpoint sampled_region iff (rst_n && access_accepted);

    cp_dir: coverpoint sampled_dir iff (rst_n && access_accepted);

    // The accept rule is the decoder's contract: only an aligned 32-bit
    // transfer gets a responder. Both reject shapes are worth a bin because a
    // firmware byte or halfword access is a realistic integration mistake.
    cp_shape: coverpoint sampled_shape iff (rst_n && access_accepted);

    // An unqualified transfer must select no endpoint at all. Covering the
    // "selected nothing" outcome records that the stimulus actually reached
    // the reject path, rather than having been filtered out upstream.
    cp_select: coverpoint any_select iff (rst_n && access_accepted) {
      bins responder_selected = {1'b1};
      bins no_responder       = {1'b0};
    }

    // The question is not which regions exist but which ones were READ and
    // which were WRITTEN: the decode hole and the aperture padding behave
    // differently per direction.
    cross_region_dir: cross cp_region, cp_dir;

    // Ties an attempted illegal shape to the region it targeted, so a reject
    // in the DEV0 CSR bank is distinguishable from one in the hub aperture.
    cross_region_shape: cross cp_region, cp_shape;

    // ---- Data phase: the response actually returned ----
    cp_resp: coverpoint resp_class(hresp) iff (rst_n && data_phase_valid && hreadyout);

    cp_resp_region: coverpoint data_phase_region
                    iff (rst_n && data_phase_valid && hreadyout);

    cp_resp_dir: coverpoint data_phase_dir
                 iff (rst_n && data_phase_valid && hreadyout);

    // The headline cross of this area. Region x direction x response class IS
    // the address-map contract: a hole that answers OKAY, or an implemented
    // region that answers ERROR, shows up here as an unexpected bin hit.
    cross_region_dir_resp: cross cp_resp_region, cp_resp_dir, cp_resp;

    // The architected default response is a two-cycle sequence. Covering the
    // phases separately, plus the transition between them, records that the
    // full sequence occurred; a single-phase error would be a protocol
    // violation.
    cp_error_phase: coverpoint {error_final_phase, error_first_phase} iff (rst_n) {
      bins first_phase       = {2'b01};
      bins final_phase       = {2'b10};
      bins sequence_complete = (2'b01 => 2'b10);
    }
  endgroup

  // ---------------------------------------------------------------------------
  // Hub bank word classes
  // ---------------------------------------------------------------------------
  // Finer-grained than the region coverpoint on purpose. Inside the hub bank
  // the word classes have genuinely different access semantics: self-initialized
  // descriptor words, the always-writable CONTROL register, the SETUP-match
  // table link pointer, and the out-of-range words that read zero. "The hub
  // region was accessed" does not answer which of those was reached.
  covergroup usb_hub_word_access_cg @(posedge clk);
    option.per_instance = 1;
    option.name         = "usb_hub_word_access";

    cp_word_class: coverpoint hub_word_class(hub_word_addr, HUB_WORDS)
                   iff (rst_n && hub_hsel);

    cp_dir: coverpoint sampled_dir iff (rst_n && hub_hsel);

    cross_word_class_dir: cross cp_word_class, cp_dir;
  endgroup

  usb_combo_access_cg      usb_combo_access_cg_inst      = new();
  usb_hub_word_access_cg   usb_hub_word_access_cg_inst   = new();

endmodule : usb_addr_cov

// File contains AI-generated response based on internal company sources
