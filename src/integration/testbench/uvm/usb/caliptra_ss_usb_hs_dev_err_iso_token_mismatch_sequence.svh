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
// Token-direction mismatch while an isochronous transaction is still
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
// ROOT CAUSE OF THE ORIGINAL (SUPERSEDED) DESIGN'S FAILURE
//
// An earlier version of this file armed iso_out_pending_r/iso_in_pending_r
// with a single-transaction (non-HBW, NBYTES bits [11:10]="00") ISO
// transfer. usb_pie.m.vhdl clears iso_out_pending_r/iso_in_pending_r as
// soon as iso_transact_cnt_down reaches "00" after a transaction completes
// (see USB_PROT_OUT_SETUP_RCV_DATA_PACKET's CRC-valid branch for OUT,
// ~line 2951, and USB_PROT_IN_TX_CRC16_BYTE2 for IN, ~line 3086). For a
// single-transaction transfer that happens on the very first data phase,
// so by the time the FSM returns to USB_PROT_WF_TOKEN_BYTE3 waiting for a
// new token, the pending flag has ALREADY cleared - the mismatched token
// can never land in the "unexpected" window. This is why the original
// design never actually hit any of the four target lines.
//
// THE FIX: BOTH EP2 OUT AND EP2 IN ARE 2-TRANSACTION HBW ENDPOINTS
//
// The firmware (caliptra_ss_usb_hs_dev_err_iso_token_mismatch.c) now arms
// both EP2 OUT and EP2 IN with NBYTES bits [11:10]="01" (2-transaction high
// bandwidth). iso_transact_cnt_down then loads to "01" and only DECREMENTS
// to "00" when the first of the two transactions completes -
// iso_out_pending_r/iso_in_pending_r stay asserted across the token
// boundary, exactly the window the mismatched token needs. This sequence
// drives only the FIRST (legitimate) transaction of each 2-transaction
// endpoint, then substitutes a mismatched token for what would have been
// the second transaction's token.
//
// WHY THE OUT-SIDE ARMING DATA PHASE MUST BE PID_MDATA, NOT PID_DATA0/1
//
// usb_pie.m.vhdl's USB_PROT_OUT_SETUP_WF_RX_DATA_PID case statement (the
// "iso_out_pending_r = '1'" branch, ~line 2646) requires the data PID to
// match the current transaction count: with iso_transact_cnt_down loaded to
// "01" (2-transaction bucket), PID_MDATA's guard
// ("iso_transact_cnt_down = 00 or iso_mdata_cnt_up = 10") is false on the
// first packet, so MDATA is ACCEPTED and increments iso_mdata_cnt_up to
// "01" WITHOUT clearing iso_transact_cnt_down (only the LAST-transaction
// branches - DATA2/DATA1/DATA0 - assert clear_iso_transact_cnt_down). At
// the subsequent CRC-valid completion (~line 2951), iso_transact_cnt_down
// is still "01" (not "00"), so the RTL takes the decr_iso_transact_cnt_down
// branch rather than clear_iso_out_pending - iso_out_pending_r survives.
// Any other PID (DATA0/DATA1/DATA2) on the first packet of a "01"-bucket
// transfer either marks the transaction as the LAST one (clearing
// iso_out_pending_r immediately, reproducing the original bug) or is
// rejected outright as pid_unknown (0x2), not the target packet_unexpected
// (0x3). MDATA is therefore the only PID that both completes normally and
// preserves iso_out_pending_r for the mismatched token that follows.
//
// WHY THE IN-SIDE ARMING STEP NEEDS NO EXPLICIT DATA-PID CONSTRUCTION
//
// EP2 IN is device-to-host: the DUT itself selects the DATAx PID to
// transmit, keyed directly on iso_transact_cnt_down
// (USB_PROT_IN_TX_DATA_PID_1/_2, ~line 3010/3037) - "00"->DATA0,
// "01"->DATA1, others->DATA2. A bare directed IN token is therefore enough
// to elicit the DUT's own correctly-sequenced first response; at
// USB_PROT_IN_TX_CRC16_BYTE2 (~line 3086) the same "01" count only
// decrements (decr_iso_transact_cnt_down), leaving iso_in_pending_r = '1'
// for the mismatched OUT token that follows.
//
// WHY NO EXCEPTION IS INJECTED ON THE MISMATCHED TOKENS
//
// Every one of the four mismatched tokens is a perfectly legal, well-formed
// TOKEN packet. The error is purely about WHEN it arrives relative to the
// pending ISO flags, not how it is built - the same "sequencing error"
// category as caliptra_ss_usb_hs_dev_err_iso_pid_seq and
// caliptra_ss_usb_hs_dev_err_toggle. attach_exception stays cleared on
// every packet this sequence sends, including the legitimate arming
// phases.
//
// WHY EVERYTHING IS DRIVEN ON THE RAW PACKET SEQUENCER
//
// The VIP's svt_usb_transfer API has no way to send a bare MDATA-only
// first phase of a multi-transaction HBW transfer, nor to request "send
// this token before the DUT believes the pending ISO phase has cleared."
// Both the legitimate arming phases and the deliberately out-of-turn
// mismatched tokens are therefore driven directly on the packet sequencer
// via caliptra_ss_usb_err_inject_packet_sequence, each OUT-side arming
// phase preceded by its own directed OUT token (same pattern as
// caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw_sequence's send_data_phase()).
//
// NO HANDSHAKE IS EXPECTED FOR THE MISMATCHED TOKENS
//
// All four target branches end in set_pie_endtransfer/clear_pie_success and
// return the FSM to USB_PROT_WF_IDLE without reaching a DMA/ACK step (same
// as every other 0x3 site - isochronous transfers never carry a handshake,
// USB 2.0 section 8.5.5), so none of the four directed mismatched tokens is
// answered.
// =============================================================================

class caliptra_ss_usb_hs_dev_err_iso_token_mismatch_sequence
    extends caliptra_ss_usb_err_inject_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_err_iso_token_mismatch_sequence)

    string MSG_ID = "USB_ERR_ISO_TOK_MISMATCH";

    // Same EP2 ISO OUT/IN slot/anchor convention as the rest of this family.
    localparam int EP2_ISO    = 2;

    // Bound on how long to wait for each arming/mismatched packet to
    // (not) complete. Same style/value as the analogous bounds in
    // err_iso_pid_seq_hbw_sequence.
    localparam realtime RESPONSE_BOUND = 200us;

    function new(string name = "caliptra_ss_usb_hs_dev_err_iso_token_mismatch_sequence");
        super.new(name);
        inject_on_label = "";
    endfunction

    // Arms iso_out_pending_r = '1' and leaves it set by completing exactly
    // the first transaction of the 2-transaction HBW EP2 OUT endpoint: a
    // directed OUT token followed by a legitimate PID_MDATA data phase -
    // see the file header's "WHY THE OUT-SIDE ARMING DATA PHASE MUST BE
    // PID_MDATA" section.
    protected task arm_iso_out(svt_usb_configuration usb_cfg, string label);
        caliptra_ss_usb_err_inject_packet_sequence tok_seq;
        caliptra_ss_usb_err_inject_packet_sequence data_seq;
        bit [7:0]                                  payload[$];
        bit                                        sent;

        tok_seq = caliptra_ss_usb_err_inject_packet_sequence::type_id::create(
            {label, "_tok_seq"});
        tok_seq.pid                  = svt_usb_packet::OUT;
        tok_seq.device_address       = 7'(USBDC0_ADDR);
        tok_seq.endpoint_number      = 4'(EP2_ISO);
        tok_seq.payload_bytes.delete();
        tok_seq.packet_configuration = usb_cfg;
        tok_seq.attach_exception     = 1'b0;
        tok_seq.msg_id               = MSG_ID;

        `uvm_info(MSG_ID,
            $sformatf("[%s] Sending directed OUT token to addr %0d ep %0d to arm iso_out_pending_r.",
                      label, USBDC0_ADDR, EP2_ISO), UVM_LOW)

        tok_seq.start(p_sequencer.usb_20_pkt_sequencer);

        payload.delete();
        for (int unsigned i = 0; i < 1024; i++)
            payload.push_back(8'(i));

        data_seq = caliptra_ss_usb_err_inject_packet_sequence::type_id::create(
            {label, "_data_seq"});
        data_seq.pid                  = svt_usb_packet::MDATA;
        data_seq.device_address       = 7'(USBDC0_ADDR);
        data_seq.endpoint_number      = 4'(EP2_ISO);
        data_seq.payload_bytes        = payload;
        data_seq.packet_configuration = usb_cfg;
        data_seq.attach_exception     = 1'b0;
        data_seq.msg_id               = MSG_ID;

        `uvm_info(MSG_ID,
            $sformatf("[%s] Sending legitimate MDATA (1st of 2 transactions) to addr %0d ep %0d.",
                      label, USBDC0_ADDR, EP2_ISO), UVM_LOW)

        sent = 1'b0;
        fork : bounded_arm_out
            begin
                data_seq.start(p_sequencer.usb_20_pkt_sequencer);
                sent = 1'b1;
            end
            begin
                #RESPONSE_BOUND;
            end
        join_any
        disable bounded_arm_out;

        if (!sent) begin
            data_seq.kill();
            `uvm_info(MSG_ID,
                $sformatf("[%s] MDATA arming packet did not complete within the response bound.",
                          label), UVM_LOW)
        end

        // No settle delay here, deliberately: the RTL's PID_SOF branch in
        // USB_PROT_WF_TOKEN_BYTE3 (usb_pie.m.vhdl ~line 2290) unconditionally
        // clears iso_out_pending_r/iso_in_pending_r on EVERY SOF, regardless
        // of whether they were legitimately pending. The periodic HS SOF
        // (125 us microframe cadence) races against the window between
        // arming and the mismatched token; any added delay here only grows
        // the chance one slips in and clears the flag before
        // send_mismatched_token() runs. The mismatched token is sent
        // immediately after this task returns - see body().
    endtask

    // Arms iso_in_pending_r = '1' and leaves it set by eliciting exactly
    // the first (DUT-generated) transaction of the 2-transaction HBW EP2
    // IN endpoint: a bare directed IN token is enough - see the file
    // header's "WHY THE IN-SIDE ARMING STEP NEEDS NO EXPLICIT DATA-PID
    // CONSTRUCTION" section.
    protected task arm_iso_in(svt_usb_configuration usb_cfg, string label);
        caliptra_ss_usb_err_inject_packet_sequence tok_seq;
        bit                                        sent;

        tok_seq = caliptra_ss_usb_err_inject_packet_sequence::type_id::create(label);
        tok_seq.pid                  = svt_usb_packet::IN;
        tok_seq.device_address       = 7'(USBDC0_ADDR);
        tok_seq.endpoint_number      = 4'(EP2_ISO);
        tok_seq.payload_bytes.delete();
        tok_seq.packet_configuration = usb_cfg;
        tok_seq.attach_exception     = 1'b0;
        tok_seq.msg_id               = MSG_ID;

        `uvm_info(MSG_ID,
            $sformatf("[%s] Sending directed IN token to addr %0d ep %0d to arm iso_in_pending_r (1st of 2 transactions).",
                      label, USBDC0_ADDR, EP2_ISO), UVM_LOW)

        sent = 1'b0;
        fork : bounded_arm_in
            begin
                tok_seq.start(p_sequencer.usb_20_pkt_sequencer);
                sent = 1'b1;
            end
            begin
                #RESPONSE_BOUND;
            end
        join_any
        disable bounded_arm_in;

        if (!sent) begin
            tok_seq.kill();
            `uvm_info(MSG_ID,
                $sformatf("[%s] IN arming token did not complete within the response bound.",
                          label), UVM_LOW)
        end

        // No settle delay here, deliberately: the RTL's PID_SOF branch in
        // USB_PROT_WF_TOKEN_BYTE3 (usb_pie.m.vhdl ~line 2290) unconditionally
        // clears iso_in_pending_r/iso_out_pending_r on EVERY SOF, regardless
        // of whether they were legitimately pending. The periodic HS SOF
        // (125 us microframe cadence) races against the window between
        // arming and the mismatched token; any added delay here only grows
        // the chance one slips in and clears the flag before
        // send_mismatched_token() runs. The mismatched token is sent
        // immediately after this task returns - see body().
    endtask

    // Sends one directed, unmodified token to EP2 while an ISO pending flag
    // is expected to still be '1', and bounds the wait for any reply (none
    // is expected - see the file header).
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
                #RESPONSE_BOUND;
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
        arm_iso_out(usb_cfg, "arm_out_r0");
        send_mismatched_token(usb_cfg, svt_usb_packet::IN,    "in_mismatch_seq");
        #ERROR_SETTLE_DELAY;

        // --- Site 2231: PID_SETUP while iso_out_pending_r = '1' -----------
        arm_iso_out(usb_cfg, "arm_out_r1");
        send_mismatched_token(usb_cfg, svt_usb_packet::SETUP, "setup_mismatch_seq");
        #ERROR_SETTLE_DELAY;

        // --- Site 2251: PID_PING while iso_out_pending_r = '1' ------------
        arm_iso_out(usb_cfg, "arm_out_r2");
        send_mismatched_token(usb_cfg, svt_usb_packet::PING,  "ping_mismatch_seq");
        #ERROR_SETTLE_DELAY;

        // --- Site 2211: PID_OUT while iso_in_pending_r = '1' --------------
        arm_iso_in(usb_cfg, "arm_in_r0");
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
