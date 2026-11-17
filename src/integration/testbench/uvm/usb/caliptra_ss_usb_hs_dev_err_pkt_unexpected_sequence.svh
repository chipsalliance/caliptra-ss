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

    // -------------------------------------------------------------------------
    // Phases A-D: the four token-mismatch blocks at usb_pie.m.vhdl lines
    // 2192-2261 (USB_PROT_WF_TOKEN_BYTE3, case pid_r). Each needs an ISO
    // pending flag set (iso_out_pending_r for phase A, iso_in_pending_r for
    // phase B, either for C/D) at the instant a mismatching token PID
    // arrives. Firmware enters phase_mode after its second EP2 OUT
    // completion and from then on keeps EP2 OUT (and, once phase B starts,
    // EP2 IN) continuously re-armed - see caliptra_ss_usb_hs_dev_err_
    // pkt_unexpected.c main(). This gives each phase a live ISO stream to
    // start a transaction on and inject the mismatching token into before
    // the microframe boundary clears the pending flag.
    //
    // send_mismatched_token() drives the token directly on the packet
    // sequencer with no exception attached - this is a sequencing error, not
    // a wire corruption, exactly as caliptra_ss_usb_err_inject_base_sequence
    // documents for "SENDING WITHOUT AN EXCEPTION".
    // -------------------------------------------------------------------------
    localparam int EP2_IN_ANCHOR = 1;

    // Time from the start of an ISO OUT/IN data phase to the mismatching
    // token injection. This is the race called out in the prompt: the token
    // must land after the pending flag is set (first byte of the data
    // phase) and before the SOF/microframe boundary or the DMA handler
    // clears it. Chosen as a fraction of ISO_TURNAROUND_DELAY, with
    // ERROR_SETTLE_DELAY as the smallest unit available from the base class.
    localparam realtime TOKEN_MISMATCH_DELAY = 5us;

    protected task send_mismatched_token(svt_usb_configuration usb_cfg,
                                         svt_usb_packet::pid_name_enum pid,
                                         string label);
        caliptra_ss_usb_err_inject_packet_sequence tok_seq;

        tok_seq = caliptra_ss_usb_err_inject_packet_sequence::type_id::create(
            "mismatch_tok_seq");
        tok_seq.pid                  = pid;
        tok_seq.device_address       = 7'(USBDC0_ADDR);
        tok_seq.endpoint_number      = 4'(EP2_ISO);
        tok_seq.payload_bytes.delete();
        tok_seq.packet_configuration = usb_cfg;
        tok_seq.attach_exception     = 1'b0;
        tok_seq.msg_id               = MSG_ID;

        `uvm_info(MSG_ID,
            $sformatf("%s: sending mismatching %s token to addr %0d EP%0d.",
                      label, pid.name(), USBDC0_ADDR, EP2_ISO), UVM_LOW)

        tok_seq.start(p_sequencer.usb_20_pkt_sequencer);
    endtask

    // Phase A: ISO OUT pending (iso_out_pending_r=1), inject PID_IN.
    protected task do_phase_a(svt_usb_agent host_agent_h,
                              svt_usb_configuration usb_cfg);
        fork
            do_iso_out(host_agent_h, usb_cfg, "PhaseA_ISO_OUT_start", 8'hA0);
            begin
                #TOKEN_MISMATCH_DELAY;
                send_mismatched_token(usb_cfg, svt_usb_packet::IN,
                                      "PhaseA");
            end
        join
        #ERROR_SETTLE_DELAY;
    endtask

    // Phase B: ISO IN pending (iso_in_pending_r=1), inject PID_OUT. Needs
    // the ISO IN endpoint, which only exists once firmware's phase_mode has
    // armed EP2 IN (slot [1] in the test's endpoint_cfg layout).
    protected task do_phase_b(svt_usb_agent host_agent_h,
                              svt_usb_configuration usb_cfg);
        svt_usb_transfer req;

        fork
            begin
                `uvm_info(MSG_ID, "PhaseB: ISO IN read on EP2.", UVM_LOW)

                do_data_xfer(
                    .agent_h         (host_agent_h),
                    .usb_cfg         (usb_cfg),
                    .xfer_kind       (svt_usb_transfer::ISOCHRONOUS_IN_TRANSFER),
                    .device_addr     (USBDC0_ADDR),
                    .ep_num          (EP2_ISO),
                    .byte_count      (HS_ISO_MAX_PACKET),
                    .ep_anchor_idx   (EP2_IN_ANCHOR),
                    .label           ("PhaseB_ISO_IN"),
                    .req             (req),
                    .single_isoc_txn (1));
            end
            begin
                #TOKEN_MISMATCH_DELAY;
                send_mismatched_token(usb_cfg, svt_usb_packet::OUT,
                                      "PhaseB");
            end
        join_any
        #ERROR_SETTLE_DELAY;
    endtask

    // Phase C: either pending flag set, inject PID_SETUP.
    protected task do_phase_c(svt_usb_agent host_agent_h,
                              svt_usb_configuration usb_cfg);
        fork
            do_iso_out(host_agent_h, usb_cfg, "PhaseC_ISO_OUT_start", 8'hC0);
            begin
                #TOKEN_MISMATCH_DELAY;
                send_mismatched_token(usb_cfg, svt_usb_packet::SETUP,
                                      "PhaseC");
            end
        join
        #ERROR_SETTLE_DELAY;
    endtask

    // Phase D: either pending flag set, inject PID_PING.
    protected task do_phase_d(svt_usb_agent host_agent_h,
                              svt_usb_configuration usb_cfg);
        fork
            do_iso_out(host_agent_h, usb_cfg, "PhaseD_ISO_OUT_start", 8'hD0);
            begin
                #TOKEN_MISMATCH_DELAY;
                send_mismatched_token(usb_cfg, svt_usb_packet::PING,
                                      "PhaseD");
            end
        join
        #ERROR_SETTLE_DELAY;
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

        // Transfer 3: this is the SECOND EP2 OUT completion from firmware's
        // point of view (the first was transfer 1 above; transfer 2 was
        // discarded with no completion since the endpoint was un-armed).
        // Firmware's second completion flips it into phase_mode, where it
        // keeps re-arming EP2 OUT/IN continuously - see main() in the .c
        // file. This transfer exists purely to generate that second
        // completion so phases A-D below have a live ISO stream to work
        // with.
        do_iso_out(host_agent_h, usb_cfg, "HS_ISO_OUT_EP2_rearm_for_phases",
                   8'hAA);
        #ISO_TURNAROUND_DELAY;

        // Phases A-D: the four token-mismatch blocks (lines 2192-2261).
        do_phase_a(host_agent_h, usb_cfg);
        do_phase_b(host_agent_h, usb_cfg);
        do_phase_c(host_agent_h, usb_cfg);
        do_phase_d(host_agent_h, usb_cfg);

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
