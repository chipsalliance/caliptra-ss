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

`ifndef CALIPTRA_SS_USB_HS_DEV_ERR_PKT_UNEXPECTED_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_ERR_PKT_UNEXPECTED_SEQUENCE_SV

// =============================================================================
// Unexpected-packet error on an isochronous OUT to USBDC0 (High Speed).
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype, bin packet_unexpected (0x3).
//
// WHY THIS TEST IS ISOCHRONOUS AND NOT BULK
//
// 0x3 looks like a generic protocol-sequencing code, but it is not: every one
// of its seven live assignment sites in usb_pie.m.vhdl is reachable only while
// an isochronous transaction is outstanding. Measured from the RTL:
//
//   line 2192  PID_IN   received while iso_out_pending_r = '1'
//   line 2211  PID_OUT  received while iso_in_pending_r  = '1'
//   line 2231  PID_SETUP received while either iso pending flag is set
//   line 2251  PID_PING received while either iso pending flag is set
//   line 2295  PID_SOF  received while either iso pending flag is set
//   line 2837  iso OUT data packet to a STALLed endpoint
//   line 2879  iso OUT data packet to an endpoint with ACTIVE clear
//
// The two iso pending flags are set ONLY on the isochronous paths - line 2500
// sets set_iso_out_pending under "if epinfo_iso = '1'", and epinfo_iso is
// latched from the endpoint list entry type bits by usb_dma.m.vhdl. On a bulk
// endpoint both flags stay low and all five token-mismatch branches are dead.
// A bulk sequencing error therefore cannot reach this bin, which is why this
// test uses an ISO endpoint even though the rest of the error family is bulk.
//
// WHICH OF THE SEVEN SITES THIS SEQUENCE TARGETS
//
// Line 2879, the "endpoint with ACTIVE clear" branch, because it is the only
// one that is deterministic from the host side alone. The five token-mismatch
// branches need a token to arrive inside the window where a previous iso
// transaction is still pending, which is a race against the SOF boundary and
// the DMA handler, and line 2837 additionally needs the endpoint STALLed,
// which is already covered by the sent_stall test.
//
// So the stimulus is again split between firmware and sequence, exactly as in
// caliptra_ss_usb_hs_dev_err_stall_sequence:
//
//   firmware  arms EP2 as an ISOCHRONOUS OUT endpoint (ACTIVE set, periodic
//             type, rate-feedback bit clear - see USB_EP_ENTRY_TYPE_PERIODIC
//             and USB_EP_ENTRY_RF_ISO in test_suites/libs/usb/usb.h) and then
//             deliberately does NOT re-arm it, leaving ACTIVE clear for the
//             second transfer.
//   sequence  sends TWO isochronous OUT transfers. The first is consumed
//             normally and clears ACTIVE in hardware; the second arrives at an
//             endpoint whose ACTIVE is now low, which is the 2879 branch.
//
// NO EXCEPTION IS INJECTED
//
// Both packets are perfectly formed. That is the point: 0x3 is not a
// corruption, it is a packet that is legal but arrives when the endpoint
// cannot take it. Isochronous transfers carry no handshake at all (USB 2.0
// section 8.5.5), so neither transfer gets ACKed or NAKed and no status check
// is run on either one. The evidence is the coverage bin.
// =============================================================================

class caliptra_ss_usb_hs_dev_err_pkt_unexpected_sequence
    extends caliptra_ss_usb_err_inject_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_err_pkt_unexpected_sequence)

    string MSG_ID = "USB_ERR_PKT_UNEXP";

    // EP2 is the isochronous endpoint the existing ISO tests use, with the
    // same anchor index convention - see caliptra_ss_usb_hs_dev_iso_out_sequence
    // which drives .ep_num(2) / .ep_anchor_idx(2).
    localparam int EP2_ISO    = 2;
    localparam int EP2_ANCHOR = 2;

    // HS isochronous max packet is 1024 bytes (USB 2.0 table 5-7), matching
    // USB_HS_DEV_ISO_BYTES in the existing ISO sequence.
    localparam int unsigned HS_ISO_MAX_PACKET = 1024;

    // Time between the two transfers. Long enough for hardware to retire the
    // first one and clear ACTIVE, and for the firmware poll loop to run and
    // decline to re-arm. 100 us is the value the existing ISO sequence uses
    // for the equivalent firmware turnaround.
    localparam realtime ISO_TURNAROUND_DELAY = 100us;

    function new(string name = "caliptra_ss_usb_hs_dev_err_pkt_unexpected_sequence");
        super.new(name);
        // Nothing is corrupted, so no label is registered for decoration.
        inject_on_label = "";
    endfunction

    // Local helper rather than the base-class bulk helpers, because this is the
    // only sequence in the family that drives an isochronous endpoint and needs
    // single_isoc_txn set.
    protected task do_iso_out(svt_usb_agent         host_agent_h,
                              svt_usb_configuration usb_cfg,
                              string                label,
                              bit [7:0]             pattern_base);
        svt_usb_transfer req;
        bit [7:0]        data[];

        data = new[HS_ISO_MAX_PACKET];
        foreach (data[i]) data[i] = 8'((i + pattern_base) % 256);

        `uvm_info(MSG_ID,
            $sformatf("%s: ISO OUT of %0d bytes to addr %0d EP%0d.",
                      label, HS_ISO_MAX_PACKET, USBDC0_ADDR, EP2_ISO), UVM_LOW)

        do_data_xfer(
            .agent_h         (host_agent_h),
            .usb_cfg         (usb_cfg),
            .xfer_kind       (svt_usb_transfer::ISOCHRONOUS_OUT_TRANSFER),
            .device_addr     (USBDC0_ADDR),
            .ep_num          (EP2_ISO),
            .byte_count      (HS_ISO_MAX_PACKET),
            .ep_anchor_idx   (EP2_ANCHOR),
            .label           (label),
            .req             (req),
            .payload_data    (data),
            .single_isoc_txn (1));
    endtask

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        bit                   ok;

        `uvm_info(MSG_ID,
            "Starting unexpected-packet scenario on EP2 isochronous OUT.",
            UVM_LOW)

        err_inject_bringup(host_agent_h, usb_cfg, MSG_ID, ok);
        if (!ok) return;

        // Transfer 1: consumed normally. This is what clears ACTIVE in
        // hardware and so sets up the condition the second transfer hits.
        do_iso_out(host_agent_h, usb_cfg, "HS_ISO_OUT_EP2_armed", 8'h00);

        #ISO_TURNAROUND_DELAY;

        // Transfer 2: same endpoint, now un-armed. usb_pie.m.vhdl line 2879.
        do_iso_out(host_agent_h, usb_cfg, "HS_ISO_OUT_EP2_unarmed", 8'h55);

        #ERROR_SETTLE_DELAY;

        // Release the MCU. These firmware images have no completion event
        // of their own - a corrupted packet is meant to be discarded - so
        // without this they poll to USB_ERR_POLL_TIMEOUT and the simtime is
        // set by that loop count rather than by the stimulus. See
        // request_mcu_stop() in caliptra_ss_usb_err_inject_base_sequence.
        request_mcu_stop(MSG_ID);

        `uvm_info(MSG_ID,
            "Unexpected-packet scenario complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_ERR_PKT_UNEXPECTED_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
