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


module caliptra_ss_usb_ocp_collision_bind;

bind caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_ocp_recovery
    caliptra_ss_usb_ocp_collision_if collision_monitor (
        .clk          (clk          ),
        .rst_ni       (rst_ni       ),
        .usb_req      (usb_req_now  ),
        .usb_ack      (usb_rb_ack   ),
        .usb_err      (usb_rb_err   ),
        .usb_write    (usb_rb_wr    ),
        .usb_cmd      (usb_rb_cmd   ),
        .usb_offset   (usb_rb_offset),
        .usb_wdata    (usb_rb_wdata ),
        .usb_wstrb    (usb_rb_wstrb ),
        .ahb_dv       (ahb_dv       ),
        .ahb_hld      (ahb_hld      ),
        .ahb_err      (ahb_err      ),
        .ahb_write    (ahb_write    ),
        .ahb_addr     (ahb_addr     ),
        .ahb_wdata    (ahb_wdata    ),
        .ahb_rdata    (ahb_rdata    ),
        .cpuif_req    (cpuif_req    ),
        .cpuif_rdata  (cpuif_rd_data),
        .recovery_ctrl({8'h00,
                        rb_hwif_out.RECOVERY_CTRL.ACTIVATE_REC_IMG.value,
                        rb_hwif_out.RECOVERY_CTRL.REC_IMG_SEL.value,
                        rb_hwif_out.RECOVERY_CTRL.CMS.value})
    );

endmodule
