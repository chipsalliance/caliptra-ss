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
// Attaches the USB functional coverage observers to the design.
//
// Both binds below target a SystemVerilog MODULE TYPE, not a hierarchy path.
// A bind resolves its port expressions in the target module's own scope, so
// every identifier on the right-hand side of a port connection below is a
// signal or parameter declared inside that target module. Consequences:
//
//   - No testbench path appears anywhere in this file, so the same file is
//     compiled unchanged into the subsystem bench (caliptra_ss_top_tb) and the
//     compound unit bench (usb_top_tb).
//   - The observers attach to EVERY instance of the target module, so a future
//     second compound instance is covered automatically.
//   - The resulting covergroup and bin names are identical in both benches,
//     which is what lets URG merge the two coverage databases with no manual
//     mapping (see tools/merge_coverage.py).
//
// VHDL-internal observation is NOT done here: bind cannot target a VHDL
// entity. Those signals are supplied by a bench-specific probe module that
// instantiates usb_hub_cov with cross-module references; see
// src/integration/testbench/usb_cov_probe_caliptra_ss.sv.
//
// The whole file is guarded by USB_FCOV so a build without the define carries
// no coverage instrumentation at all.
module usb_cov_bind;

`ifdef USB_FCOV

  // ---------------------------------------------------------------------------
  // Address space and access semantics
  // ---------------------------------------------------------------------------
  // The decoder publishes its own aperture geometry as localparams, so the
  // observer is parameterized from the target rather than from a duplicated
  // constant that could drift.
  bind usb_compound_ahb_decoder usb_addr_cov #(
    .HUB_WORDS          (C_HUB_FIFO_SIZE),
    .HUB_APERTURE_BYTES (32'(HUB_APERTURE_BYTES))
  ) u_usb_addr_cov (
    .clk                  (clk),
    .rst_n                (rst_n),

    // Address phase. addr_phase_active and addr_phase_byte_addr are the
    // decoder's own qualified decode nets, so the observer sees exactly the
    // address the decoder acted on.
    .addr_phase_active    (addr_phase_active),
    .addr_phase_byte_addr (32'(addr_phase_byte_addr)),
    .hsize                (combo_hsize),
    .haddr_low            (combo_haddr[1:0]),
    .hwrite               (combo_hwrite),
    .hready               (combo_hready),

    // Downstream selects and the hub word address the decoder derived.
    .dev0_csr_hsel        (dev0_csr_hsel),
    .hub_hsel             (hub_hsel),
    .recovery_hsel        (recovery_hsel),
    .hub_word_addr        (32'(addr_phase_csr_word_addr)),

    // Data phase. The two error phases are decoded from the registered
    // responder state, which is the only place the architected two-cycle
    // error sequence is visible.
    .hresp                (combo_hresp),
    .hreadyout            (combo_hreadyout),
    .error_first_phase    (data_phase_select_q == RESP_ERROR_FIRST),
    .error_final_phase    (data_phase_select_q == RESP_ERROR_FINAL)
  );

  // ---------------------------------------------------------------------------
  // Clock gating, reset context and the OCP claim handshake (area H)
  // ---------------------------------------------------------------------------
  // Every connection here is a wrapper PORT, which is why this observer needs
  // no hierarchy access and stays mergeable between the two benches.
  //
  // The interrupt, suspend/resume and topology ports this bind used to carry
  // were removed along with the covergroups that consumed them: those are now
  // measured per device from usb_reg_if_1/_2 by the probe-fed observers, which
  // can attribute them to a device where the merged wrapper view cannot.
  bind ip_xxx_3511_hs_mem_compound_wrapper usb_power_cov u_usb_power_cov (
    .clk                    (usb_axi_aclk),
    .rst_n                  (usb_axi_aresetn),

    .payload_available      (payload_available),
    .ocp_firmware_activated (ocp_firmware_activated),

    .usb_vbus               (USB_VBus),
    .usb_needclk            (usb_needclk),

    .utmi_suspendm          (utmi_suspendm),
    .utmi_reset             (utmi_reset),
    .utmi_txvalid           (utmi_txvalid),
    .utmi_linestate         (utmi_linestate)
  );

`endif // USB_FCOV

endmodule : usb_cov_bind

// File contains AI-generated response based on internal company sources
