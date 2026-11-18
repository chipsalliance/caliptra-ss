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

`ifndef CALIPTRA_SS_USB_HS_DEV_ERR_ISO_TOKEN_MISMATCH_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_ERR_ISO_TOKEN_MISMATCH_SEQUENCE_SV

// =============================================================================
// Token-direction mismatch while an isochronous OUT transaction is still
// pending, USBDC0, High Speed.
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype bin packet_unexpected (0x3) - the
// SAME bin caliptra_ss_usb_hs_dev_err_pkt_unexpected and
// caliptra_ss_usb_hs_dev_err_iso_stalled already close. This test adds NO
// new bin-level coverage. Its only purpose is RTL LINE/BRANCH coverage of
// four specific dark assignment sites in usb_pie.m.vhdl that none of the
// existing nine original tests, nor the five "extended error-injection
// coverage" tests, exercise:
//
//   line 2192  PID_IN    received in USB_PROT_WF_TOKEN_BYTE3 while
//              iso_out_pending_r = '1' ("PID_OUT was expected")
//   line 2211  PID_OUT   received in USB_PROT_WF_TOKEN_BYTE3 while
//              iso_in_pending_r = '1' ("PID_IN was expected")
//   line 2231  PID_SETUP received in USB_PROT_WF_TOKEN_BYTE3 while either
//              iso pending flag is set ("PID_IN/PID_OUT was expected")
//   line 2251  PID_PING  received in USB_PROT_WF_TOKEN_BYTE3 while either
//              iso pending flag is set ("PID_IN/PID_OUT was expected")
//
// caliptra_ss_usb_hs_dev_err_pkt_unexpected's own sequence header lists all
// seven live 0x3 assignment sites (2192/2211/2231/2251/2295/2837/2879) and
// explicitly targets only 2879 (endpoint ACTIVE clear); err_iso_stalled
// targets 2837 (endpoint STALLed). This test targets the four
// "token-while-iso-pending" branches that neither of those two reaches,
// since both of them probe the endpoint state rather than racing a second
// token against iso_out_pending_r/iso_in_pending_r.
//
// WHY A BARE PID_IN IS ENOUGH TO HIT LINE 2192
//
// iso_out_pending_r is set by set_iso_out_pending (usb_pie.m.vhdl line 2524)
// as soon as the first OUT data packet of a fresh isochronous transfer is
// accepted, and stays set until the next SOF (PID_SOF clears both iso
// pending flags unconditionally at line ~2306-2310) or until the matching IN
// data phase completes. So the window to hit line 2192 is: after the ISO OUT
// data packet lands and before the next SOF. Sending a directed PID_IN token
// to the SAME endpoint inside that window takes the PID_IN branch of the
// USB_PROT_WF_TOKEN_BYTE3 case while iso_out_pending_r is still '1', which is
// exactly line 2192's guard.
//
// WHY NO EXCEPTION IS INJECTED
//
// Every one of these four tokens is a perfectly legal, well-formed TOKEN
// packet. The error is purely about WHEN it arrives relative to the pending
// ISO flags, not how it is built - the same "sequencing error" category as
// caliptra_ss_usb_hs_dev_err_iso_pid_seq and caliptra_ss_usb_hs_dev_err_toggle.
// attach_exception stays cleared on every packet this sequence sends.
//
// WHY THE ARMING TRANSFER USES do_data_xfer() BUT THE MISMATCHED TOKEN
// DOES NOT
//
// The VIP's svt_usb_transfer API always keeps a transaction's token/data/
// handshake grouped and time-ordered; it has no way to request "send this
// EP2 OUT token early, before the DUT believes the pending ISO phase has
// cleared." So the deliberately out-of-turn tokens below must be driven
// directly on the packet sequencer via caliptra_ss_usb_err_inject_packet_
// sequence. The arming ISO OUT that sets iso_out_pending_r/iso_in_pending_r
// in the first place is a completely ordinary, well-formed transfer, so it
// is driven through do_data_xfer() (the same helper
// caliptra_ss_usb_hs_dev_err_pkt_unexpected's do_iso_out() uses) so the
// VIP's transfer-routing monitor registers the device/endpoint correctly.
// An earlier version of this file drove the arming phase on the raw packet
// sequencer as well, reasoning that mixing layers was what caused
// "[register_fail:...rx_packet_routed_check] Can't tell where this packet
// should go, No device with matching address found!" in a real run - that
// was backwards: a regression run proved the raw-sequencer arming is what
// triggers rx_packet_routed_check (err_pkt_unexpected, which only ever
// arms via do_data_xfer(), never hits it), and the fix is to keep the
// arming transfer on the transfer-level API while leaving only the
// intentionally-illegal mismatched token on the raw sequencer.
//
// NO HANDSHAKE IS EXPECTED
//
// All four target branches end in set_pie_endtransfer/clear_pie_success and
// return the FSM to USB_PROT_WF_IDLE without reaching a DMA/ACK step (same
// as every other 0x3 site - isochronous transfers never carry a handshake,
// USB 2.0 section 8.5.5), so none of the four directed tokens is answered.
// =============================================================================

class caliptra_ss_usb_hs_dev_err_iso_token_mismatch_sequence
    extends caliptra_ss_usb_err_inject_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_err_iso_token_mismatch_sequence)

    string MSG_ID = "USB_ERR_ISO_TOK_MISMATCH";

    // Same EP2 ISO OUT slot/anchor convention as err_pkt_unexpected,
    // err_iso_stalled and err_iso_pid_seq.
    localparam int EP2_ISO    = 2;
    localparam int EP2_ANCHOR = 2;

    // HS isochronous max packet (USB 2.0 table 5-7), matching the existing
    // ISO sequences in this family.
    localparam int unsigned HS_ISO_MAX_PACKET = 1024;

    // Bound on how long to wait for each mismatched token to (not) complete.
    // Same style/value as the analogous bound in err_iso_pid_seq_sequence.
    localparam realtime MISMATCH_RESPONSE_BOUND = 200us;

    function new(string name = "caliptra_ss_usb_hs_dev_err_iso_token_mismatch_sequence");
        super.new(name);
        inject_on_label = "";
    endfunction

    // Arms the DUT into iso_out_pending_r = '1' by driving one ordinary ISO
    // OUT transfer (data phase only, no exception) through the
    // transfer-level do_data_xfer() helper - see the file header's
    // "WHY THE ARMING TRANSFER USES do_data_xfer()" section for why this is
    // required instead of driving the arming phase on the raw packet
    // sequencer.
    protected task do_iso_out(svt_usb_agent         host_agent_h,
                              svt_usb_configuration usb_cfg,
                              string                label);
        svt_usb_transfer req;
        bit [7:0]        data[];

        data = new[HS_ISO_MAX_PACKET];
        foreach (data[i]) data[i] = 8'(i % 256);

        `uvm_info(MSG_ID,
            $sformatf("%s: ISO OUT of %0d bytes to addr %0d EP%0d, to arm iso_out_pending_r.",
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


    // Sends one directed, unmodified token to EP2 while iso_out_pending_r is
    // expected to still be '1', and bounds the wait for any reply (none is
    // expected - see the file header). This deliberately out-of-turn token
    // has to stay on the raw packet sequencer - see the file header.
    protected task send_mismatched_token(svt_usb_configuration        usb_cfg,
                                          svt_usb_packet::pid_name_enum pid,
                                          string                        label);
        caliptra_ss_usb_err_inject_packet_sequence tok_seq;
        bit                                        sent;

        tok_seq = caliptra_ss_usb_err_inject_packet_sequence::type_id::create(label);
        tok_seq.pid                  = pid;
        tok_seq.device_address       = 7'(USBDC0_ADDR);
        tok_seq.endpoint_number      = 4'(EP2_ISO);
        tok_seq.payload_bytes.delete();
        tok_seq.packet_configuration = usb_cfg;
        tok_seq.attach_exception     = 1'b0;
        tok_seq.msg_id               = MSG_ID;

        `uvm_info(MSG_ID,
            $sformatf("Sending directed %s token to addr %0d ep %0d while an ISO transaction is pending.",
                      pid.name(), USBDC0_ADDR, EP2_ISO), UVM_LOW)

        sent = 1'b0;
        fork : bounded_token
            begin
                tok_seq.start(p_sequencer.usb_20_pkt_sequencer);
                sent = 1'b1;
            end
            begin
                #MISMATCH_RESPONSE_BOUND;
            end
        join_any
        disable bounded_token;

        if (!sent) begin
            tok_seq.kill();
            `uvm_info(MSG_ID,
                $sformatf("%s token did not complete within the response bound. Acceptable - the DUT returns to WF_IDLE without answering it.",
                          pid.name()), UVM_LOW)
        end
    endtask

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        bit                   ok;

        `uvm_info(MSG_ID,
            "Starting ISO token-direction mismatch scenario on EP2.",
            UVM_LOW)

        err_inject_bringup(host_agent_h, usb_cfg, MSG_ID, ok);
        if (!ok) return;

        // --- Site 2192: PID_IN while iso_out_pending_r = '1' --------------
        do_iso_out(host_agent_h, usb_cfg, "HS_ISO_OUT_EP2_r0");
        send_mismatched_token(usb_cfg, svt_usb_packet::IN,    "in_mismatch_seq");
        #ERROR_SETTLE_DELAY;

        // --- Site 2231: PID_SETUP while iso_out_pending_r = '1' -----------
        do_iso_out(host_agent_h, usb_cfg, "HS_ISO_OUT_EP2_r1");
        send_mismatched_token(usb_cfg, svt_usb_packet::SETUP, "setup_mismatch_seq");
        #ERROR_SETTLE_DELAY;

        // --- Site 2251: PID_PING while iso_out_pending_r = '1' ------------
        do_iso_out(host_agent_h, usb_cfg, "HS_ISO_OUT_EP2_r2");
        send_mismatched_token(usb_cfg, svt_usb_packet::PING,  "ping_mismatch_seq");
        #ERROR_SETTLE_DELAY;

        // --- Site 2211: PID_OUT while iso_in_pending_r = '1' --------------
        // iso_in_pending_r is set by set_iso_in_pending (usb_pie.m.vhdl line
        // 2401), reached from an IN token accepted on an isochronous
        // endpoint with epinfo_active='1' (usb_dma.m.vhdl epinfo_iso derives
        // from the descriptor's TYPE_PERIODIC bit). The firmware
        // (caliptra_ss_usb_hs_dev_err_iso_token_mismatch.c,
        // usb_ep2_in_arm_iso()) arms EP2 IN as ACTIVE and TYPE_PERIODIC with
        // NBYTES bits [11:10] = "01" so iso_in_pending_r survives this first
        // IN data packet instead of being cleared immediately - see that
        // function's header comment for the NBYTES rationale. A bare
        // directed IN token is enough to reach the accept branch and set
        // the flag before the mismatched OUT token below arrives; no data
        // payload is needed since the RTL checks the token/endpoint state,
        // not the payload content.
        send_mismatched_token(usb_cfg, svt_usb_packet::IN,    "in_arm_seq");
        send_mismatched_token(usb_cfg, svt_usb_packet::OUT,   "out_mismatch_seq");
        #ERROR_SETTLE_DELAY;

        // Release the MCU. Same rationale as every other err-injection body
        // - see request_mcu_stop() in caliptra_ss_usb_err_inject_base_sequence.
        request_mcu_stop(MSG_ID);

        `uvm_info(MSG_ID,
            "ISO token-direction mismatch scenario complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_ERR_ISO_TOKEN_MISMATCH_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
