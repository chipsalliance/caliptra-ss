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

module usb_cov_bind;
    `ifdef FCOV
    `define USB_COV_ARB u_hub_compound.usb_ocp_recovery_post_sync_arb_1
    `define USB_COV_REG u_hub_compound.usb_reg_if_1

    bind ip_xxx_3511_hs_mem_compound_wrapper usb_cov_if i_usb_cov_if (
        .hclk                       (`USB_COV_ARB.hclk),
        .hresetn                    (`USB_COV_ARB.hresetn),
        .sync_busreset              (`USB_COV_ARB.sync_busreset),
        .dev0_local_reset_c          (`USB_COV_ARB.dev0_local_reset_c),
        .new_setup_c                (`USB_COV_ARB.new_setup_c),
        .setup_owner_ocp_o           (`USB_COV_ARB.setup_owner_ocp_o),
        .post_sync_arb_state_o       (`USB_COV_ARB.post_sync_arb_state_o),
        .usbreg_setup               (`USB_COV_REG.usbreg_setup),
        .ocp_claim_abort_i           (`USB_COV_ARB.ocp_claim_abort_i),
        .fw_protocol_error_req_i     (`USB_COV_ARB.fw_protocol_error_req_i),
        .ep0_ocp_owner_r             (`USB_COV_ARB.ep0_ocp_owner_r),
        .setup_complete_c            (`USB_COV_ARB.setup_complete_c),
        .setup_valid_c               (`USB_COV_ARB.setup_valid_c),
        .setup_claim_c               (`USB_COV_ARB.setup_claim_c),
        .dma_set_int                (`USB_COV_REG.dma_set_int),
        .dma_txn_done_c              (`USB_COV_ARB.dma_txn_done_c),
        .dma_req_forward_c           (`USB_COV_ARB.dma_req_forward_c),
        .setup_dma_match_c           (`USB_COV_ARB.setup_dma_match_c),
        .sync_sieint_endtransfer_o   (`USB_COV_ARB.sync_sieint_endtransfer_o),
        .sync_sieint_success_o       (`USB_COV_ARB.sync_sieint_success_o)
    );

    `undef USB_COV_ARB
    `undef USB_COV_REG
    `endif
endmodule
