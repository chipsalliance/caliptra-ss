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

`ifndef CALIPTRA_SS_USB_HS_DEV_ERR_ISO_STALLED_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_ERR_ISO_STALLED_SEQUENCE_SV

// =============================================================================
// Isochronous OUT data packet to a STALLed endpoint on USBDC0 (High Speed).
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype, bin packet_unexpected (0x3), RTL site
// usb_pie.m.vhdl line 2837 (USB_PROT_OUT_SETUP_RCV_DATA_PACKET, the
// "epinfo_stall = '1' and epinfo_active = '0' ... iso_out_pending_r = '1'"
// branch).
//
// WHY THIS IS A DIFFERENT SITE FROM THE EXISTING err_pkt_unexpected TEST
//
// err_pkt_unexpected closes line 2879, which is reached when ACTIVE is clear
// but STALL is NOT set. Line 2837 needs BOTH epinfo_stall = '1' AND
// epinfo_active = '0' on the same ISO endpoint - the sibling branch of the
// 2816 bulk-endpoint STALL site that err_stall already closes, but taken
// instead of 2816 when the endpoint is isochronous (iso_out_pending_r = '1').
//
// iso_out_pending_r IS ALREADY '1' FOR THE PACKET BEING PROCESSED
//
// It looks like iso_out_pending_r should reflect an EARLIER pending
// transaction, but it does not have to: usb_pie.m.vhdl lines 2498-2503 set
// set_iso_out_pending as soon as an OUT data packet is accepted for an
// epinfo_iso = '1' endpoint, in the SAME state-machine pass that leads into
// USB_PROT_OUT_SETUP_RCV_DATA_PACKET where the errortype branch at 2837 is
// evaluated. So a single ISO OUT data packet to a STALLed ISO endpoint is
// sufficient - there is no need for the two-transfer "armed then unarmed"
// pattern that err_pkt_unexpected uses for its ACTIVE-clear-only site.
//
// FIRMWARE-DRIVEN, SAME SHAPE AS err_stall BUT ON AN ISO ENDPOINT
//
// epinfo_stall and epinfo_active are latched out of the EP2 OUT
// command/status list entry (USB_EP_ENTRY_STALL / USB_EP_ENTRY_ACTIVE), so
// only firmware can set them. This suite arms EP2 OUT as isochronous
// (USB_EP_ENTRY_TYPE_PERIODIC, RF_ISO) with STALL set and ACTIVE clear - the
// same two bits err_stall sets on EP1, just with the periodic/ISO type bits
// also set so epinfo_iso = '1' when the DMA handler reads the entry.
//
// NO EXCEPTION IS INJECTED
//
// The ISO OUT data packet itself is perfectly formed; the error is purely a
// function of the endpoint descriptor state the firmware wrote. Isochronous
// transfers carry no handshake (USB 2.0 section 8.5.5), so the transfer is
// not status-checked; the coverage bin is the evidence.
// =============================================================================

class caliptra_ss_usb_hs_dev_err_iso_stalled_sequence
    extends caliptra_ss_usb_err_inject_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_err_iso_stalled_sequence)

    string MSG_ID = "USB_ERR_ISO_STALLED";

    // EP2 is the isochronous endpoint the existing ISO tests use, with the
    // same anchor index convention - see caliptra_ss_usb_hs_dev_iso_out_sequence
    // and caliptra_ss_usb_hs_dev_err_pkt_unexpected_sequence.
    localparam int EP2_ISO    = 2;
    localparam int EP2_ANCHOR = 2;

    // HS isochronous max packet is 1024 bytes (USB 2.0 table 5-7).
    localparam int unsigned HS_ISO_MAX_PACKET = 1024;

    function new(string name = "caliptra_ss_usb_hs_dev_err_iso_stalled_sequence");
        super.new(name);
        // No injection at all: the error comes from the endpoint state the
        // firmware set up, same as err_stall / err_ping_stall.
        inject_on_label = "";
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_transfer      req;
        bit [7:0]             data[];
        bit                   ok;

        `uvm_info(MSG_ID,
            "Starting ISO OUT to STALLed endpoint scenario on EP2 isochronous OUT.",
            UVM_LOW)

        err_inject_bringup(host_agent_h, usb_cfg, MSG_ID, ok);
        if (!ok) return;

        data = new[HS_ISO_MAX_PACKET];
        foreach (data[i]) data[i] = i[7:0];

        `uvm_info(MSG_ID,
            $sformatf({"ISO OUT of %0d bytes to addr %0d EP%0d, which the ",
                       "firmware armed as isochronous with STALL set and ",
                       "ACTIVE clear. No handshake is the expected outcome."},
                      HS_ISO_MAX_PACKET, USBDC0_ADDR, EP2_ISO), UVM_LOW)

        do_data_xfer(
            .agent_h         (host_agent_h),
            .usb_cfg         (usb_cfg),
            .xfer_kind       (svt_usb_transfer::ISOCHRONOUS_OUT_TRANSFER),
            .device_addr     (USBDC0_ADDR),
            .ep_num          (EP2_ISO),
            .byte_count      (HS_ISO_MAX_PACKET),
            .ep_anchor_idx   (EP2_ANCHOR),
            .label           ("HS_ISO_OUT_EP2_STALLED"),
            .req             (req),
            .payload_data    (data),
            .single_isoc_txn (1));

        #ERROR_SETTLE_DELAY;

        // No recovery leg: the endpoint stays halted by design, same as
        // err_stall / err_ping_stall.
        request_mcu_stop(MSG_ID);

        `uvm_info(MSG_ID,
            "ISO OUT to STALLed endpoint scenario complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_ERR_ISO_STALLED_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
