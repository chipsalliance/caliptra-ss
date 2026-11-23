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

`ifndef CALIPTRA_SS_USB_HS_DEV_ERR_ISO_PID_SEQ_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_ERR_ISO_PID_SEQ_SEQUENCE_SV

// =============================================================================
// Out-of-sequence MDATA PID on a single-buffer isochronous OUT endpoint,
// USBDC0, High Speed.
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype bin pid_unknown (0x2), RTL site
// usb_pie.m.vhdl line 2632 (USB_PROT_OUT_SETUP_WF_RX_DATA_PID, the
// "iso_out_pending_r = '1'" case statement, PID_MDATA branch, taken when
// "iso_transact_cnt_down = '00' or iso_mdata_cnt_up = '10'").
//
// WHY MDATA ON A SINGLE-BUFFER ISO ENDPOINT IS ALWAYS "UNEXPECTED"
//
// MDATA is legal only on a HIGH-BANDWIDTH isochronous endpoint (USB 2.0
// section 5.9.2): one that can carry up to 3 x 1024-byte transactions per
// microframe (OUT: MDATA, MDATA, DATA2). iso_transact_cnt_down is loaded from
// epinfo at usb_pie.m.vhdl line ~2500 when the first OUT data packet of a
// fresh transfer is accepted (set_iso_out_pending, load_iso_transact_cnt_down
// under "if iso_out_pending_r = '0'"). The endpoint this suite arms is the
// SAME single 1024-byte-buffer EP2 OUT configuration
// caliptra_ss_usb_hs_dev_err_pkt_unexpected / err_iso_stalled already use -
// one NBYTES entry, no high-bandwidth multi-transaction setup - so
// iso_transact_cnt_down loads to "00" (single transaction) on that first
// packet. Sending MDATA as that very first data packet therefore always hits
// "iso_transact_cnt_down = '00'" and reports ERROR_PID_UNKNOWN, regardless of
// payload content.
//
// WHY A DIRECTED PACKET SEQUENCE ON THE PACKET SEQUENCER, NOT THE TRANSFER
// SEQUENCER
//
// The VIP's svt_usb_transfer API has no way to request an MDATA data PID on a
// non-high-bandwidth endpoint - the transfer layer only emits a high-bandwidth
// MDATA/DATA2 sequence when isoc_mult is configured for it (see
// src/usb/tb/sequences/usb_high_bandwidth_iso_seq.svh). So this test drives
// the OUT token and the MDATA data packet directly on the packet sequencer,
// using caliptra_ss_usb_err_inject_packet_sequence, exactly as
// inject_error_packet() already does for its is_data_pkt "prepend an OUT
// token" case in caliptra_ss_usb_err_inject_base_sequence.svh - but called
// directly here (not through inject_error_packet()) because that helper
// targets the shared bulk EP1, and this test targets the isochronous EP2.
//
// NO EXCEPTION IS INJECTED
//
// MDATA is a real, well formed PID - svt_usb_packet_exception has no
// error_kind for "legal PID, wrong sequencing position" (see the header of
// caliptra_ss_usb_err_inject_packet_sequence.svh, "SENDING WITHOUT AN
// EXCEPTION"). attach_exception is cleared on both packets; the MDATA packet
// is driven exactly as built.
//
// NO HANDSHAKE IS EXPECTED
//
// Isochronous transfers never carry a handshake (USB 2.0 section 8.5.5), and
// RTL line 2632's PID_MDATA-unexpected branch additionally clears
// iso_out_pending_r/iso_in_pending_r and returns the FSM to WF_IDLE without
// ever reaching a DMA/ACK step, so nothing on the wire answers this packet.
// =============================================================================

class caliptra_ss_usb_hs_dev_err_iso_pid_seq_sequence
    extends caliptra_ss_usb_err_inject_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_err_iso_pid_seq_sequence)

    string MSG_ID = "USB_ERR_ISO_PID_SEQ";

    // Same EP2 ISO OUT slot/anchor convention as err_pkt_unexpected and
    // err_iso_stalled.
    localparam int EP2_ISO    = 2;
    localparam int EP2_ANCHOR = 2;

    // Bound on how long to wait for the MDATA packet to (not) complete.
    // Same style/value as INJECT_RESPONSE_BOUND in the base class.
    localparam realtime MDATA_RESPONSE_BOUND = 200us;

    function new(string name = "caliptra_ss_usb_hs_dev_err_iso_pid_seq_sequence");
        super.new(name);
        inject_on_label = "";
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        bit                   ok;

        caliptra_ss_usb_err_inject_packet_sequence tok_seq;
        caliptra_ss_usb_err_inject_packet_sequence mdata_seq;
        bit [7:0]                                  payload[$];
        bit                                        sent;

        `uvm_info(MSG_ID,
            "Starting out-of-sequence MDATA scenario on EP2 isochronous OUT.",
            UVM_LOW)

        err_inject_bringup(host_agent_h, usb_cfg, MSG_ID, ok);
        if (!ok) return;

        // Directed OUT token to EP2, so the PIE is in its data phase when
        // the MDATA packet below arrives. No exception: this is a perfectly
        // legal token, same precedent as inject_error_packet()'s is_data_pkt
        // case.
        tok_seq = caliptra_ss_usb_err_inject_packet_sequence::type_id::create(
            "tok_seq");
        tok_seq.pid                  = svt_usb_packet::OUT;
        tok_seq.device_address       = 7'(USBDC0_ADDR);
        tok_seq.endpoint_number      = 4'(EP2_ISO);
        tok_seq.payload_bytes.delete();
        tok_seq.packet_configuration = usb_cfg;
        tok_seq.attach_exception     = 1'b0;
        tok_seq.msg_id               = MSG_ID;

        `uvm_info(MSG_ID,
            $sformatf({"Sending a directed OUT token to addr %0d ep %0d so ",
                       "the PIE is in its data phase when the MDATA packet ",
                       "below arrives."}, USBDC0_ADDR, EP2_ISO), UVM_LOW)

        tok_seq.start(p_sequencer.usb_20_pkt_sequencer);

        // Payload content is irrelevant - the PID itself is what the RTL
        // branch keys on, not the data bytes. One max-packet's worth keeps
        // the wire framing identical to a real ISO OUT.
        payload.delete();
        for (int unsigned i = 0; i < 1024; i++)
            payload.push_back(8'(i));

        mdata_seq = caliptra_ss_usb_err_inject_packet_sequence::type_id::create(
            "mdata_seq");
        mdata_seq.pid                  = svt_usb_packet::MDATA;
        mdata_seq.device_address       = 7'(USBDC0_ADDR);
        mdata_seq.endpoint_number      = 4'(EP2_ISO);
        mdata_seq.payload_bytes        = payload;
        mdata_seq.packet_configuration = usb_cfg;
        mdata_seq.attach_exception     = 1'b0;
        mdata_seq.msg_id               = MSG_ID;

        `uvm_info(MSG_ID,
            $sformatf({"Sending MDATA to addr %0d ep %0d - unexpected on a ",
                       "single-buffer (non high-bandwidth) ISO endpoint. No ",
                       "handshake is the expected outcome."},
                      USBDC0_ADDR, EP2_ISO), UVM_LOW)

        // The DUT returns to WF_IDLE without answering this packet at all, so
        // the start() is bounded - same guard style as
        // inject_error_packet()'s bounded_injection fork.
        sent = 1'b0;
        fork : bounded_mdata
            begin
                mdata_seq.start(p_sequencer.usb_20_pkt_sequencer);
                sent = 1'b1;
            end
            begin
                #MDATA_RESPONSE_BOUND;
            end
        join_any
        disable bounded_mdata;

        if (!sent) begin
            mdata_seq.kill();
            `uvm_info(MSG_ID,
                {"MDATA packet did not complete within the response bound. ",
                 "That is an acceptable outcome - the DUT is not obliged to ",
                 "answer an out-of-sequence ISO data PID."}, UVM_LOW)
        end

        #ERROR_SETTLE_DELAY;

        // -------------------------------------------------------------------
        // PID_DATA1 and PID_DATA2 unexpected branches (usb_pie.m.vhdl lines
        // 2655/2680). Both guards default to "unexpected" on a fresh
        // transfer on this same single-buffer endpoint, since
        // iso_mdata_cnt_up resets to "00" and:
        //   PID_DATA1: unexpected when iso_mdata_cnt_up /= "01" (HS)
        //   PID_DATA2: unexpected when iso_mdata_cnt_up /= "10" (any speed)
        // Neither needs a high-bandwidth endpoint - unlike PID_DATA0
        // (unexpected only when iso_mdata_cnt_up /= "00", which requires a
        // prior successful MDATA acceptance, impossible on this endpoint).
        // Same directed OUT-token + bare data-PID pattern as the MDATA case
        // above, no exception attached (legal PID, wrong sequencing
        // position).
        // -------------------------------------------------------------------
        send_mismatched_data_pid(usb_cfg, svt_usb_packet::DATA1, "PhaseDATA1");
        send_mismatched_data_pid(usb_cfg, svt_usb_packet::DATA2, "PhaseDATA2");

        // Release the MCU. Same rationale as every other err-injection body
        // - see request_mcu_stop() in caliptra_ss_usb_err_inject_base_sequence.
        request_mcu_stop(MSG_ID);

        `uvm_info(MSG_ID,
            "Out-of-sequence ISO data PID scenarios complete.", UVM_LOW)
    endtask

    // -------------------------------------------------------------------
    // Shared helper for the DATA1/DATA2 phases: directed OUT token to EP2
    // ISO OUT, followed by a bare data packet carrying the given PID, no
    // exception attached. Bounded the same way as the MDATA injection in
    // body() - the DUT answers neither packet (isochronous, no handshake;
    // RTL returns to WF_IDLE without a DMA/ACK step).
    // -------------------------------------------------------------------
    protected task send_mismatched_data_pid(svt_usb_configuration usb_cfg,
                                              svt_usb_packet::pid_name_enum pid,
                                              string label);
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
            $sformatf({"[%s] Sending a directed OUT token to addr %0d ep ",
                       "%0d so the PIE is in its data phase."},
                      label, USBDC0_ADDR, EP2_ISO), UVM_LOW)

        tok_seq.start(p_sequencer.usb_20_pkt_sequencer);

        payload.delete();
        for (int unsigned i = 0; i < 1024; i++)
            payload.push_back(8'(i));

        data_seq = caliptra_ss_usb_err_inject_packet_sequence::type_id::create(
            {label, "_data_seq"});
        data_seq.pid                  = pid;
        data_seq.device_address       = 7'(USBDC0_ADDR);
        data_seq.endpoint_number      = 4'(EP2_ISO);
        data_seq.payload_bytes        = payload;
        data_seq.packet_configuration = usb_cfg;
        data_seq.attach_exception     = 1'b0;
        data_seq.msg_id               = MSG_ID;

        `uvm_info(MSG_ID,
            $sformatf({"[%s] Sending %s to addr %0d ep %0d - unexpected on ",
                       "a fresh ISO transfer (iso_mdata_cnt_up resets to ",
                       "\"00\"). No handshake is the expected outcome."},
                      label, pid.name(), USBDC0_ADDR, EP2_ISO), UVM_LOW)

        sent = 1'b0;
        fork : bounded_data_pid
            begin
                data_seq.start(p_sequencer.usb_20_pkt_sequencer);
                sent = 1'b1;
            end
            begin
                #MDATA_RESPONSE_BOUND;
            end
        join_any
        disable bounded_data_pid;

        if (!sent) begin
            data_seq.kill();
            `uvm_info(MSG_ID,
                $sformatf({"[%s] %s packet did not complete within the ",
                           "response bound. That is an acceptable outcome."},
                          label, pid.name()), UVM_LOW)
        end

        #ERROR_SETTLE_DELAY;
    endtask

endclass


`endif // CALIPTRA_SS_USB_HS_DEV_ERR_ISO_PID_SEQ_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
