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

module usb_ocp_cov_bind;
  `ifdef FCOV
  // All taps are in the SV wrapper/recovery hierarchy. No cross-language
  // VHDL state access, force, or existing observer-interface dependency.
  bind ip_xxx_3511_hs_mem_compound_wrapper
    usb_ocp_cov_if #(.HUB_ADDR_WIDTH(HUB_AHB_WORD_ADDR_W)) ocp_exercise_cov (
      .clk(usb_axi_aclk),
      .rst_n(usb_axi_aresetn),
      .hub_select(hub_hsel),
      .hub_transfer(hub_htrans),
      .hub_write(hub_hwrite),
      .hub_address(hub_haddr),
      .hub_ready_in(hub_hreadyin),
      .hub_ready_out(hub_hreadyout),
      .hub_data(hub_hwdata),
      .ocp_request(u_ocp_recovery.usb_req_now),
      .fifo_push(u_ocp_recovery.u_a4_cms_fifo.fifo_wvalid &&
                 u_ocp_recovery.u_a4_cms_fifo.fifo_wready),
      .fifo_pop(u_ocp_recovery.u_a4_cms_fifo.fifo_rvalid_int &&
                u_ocp_recovery.u_a4_cms_fifo.fifo_rready_int),
      .activate(u_ocp_recovery.rb_hwif_out.RECOVERY_CTRL.ACTIVATE_REC_IMG.value)
    );
  `endif
endmodule
