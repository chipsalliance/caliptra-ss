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

`ifndef CALIPTRA_SS_USB_HS_DEV_ERR_ISO_PID_SEQ_HBW_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_ERR_ISO_PID_SEQ_HBW_SEQUENCE_SV

// =============================================================================
// Out-of-sequence DATA0 PID on a high-bandwidth (HBW) isochronous OUT
// endpoint, USBDC0, High Speed.
//
// FORKED FROM caliptra_ss_usb_hs_dev_err_iso_pid_seq, NOT AN EDIT TO IT
//
// caliptra_ss_usb_hs_dev_err_iso_pid_seq deliberately uses a single-buffer,
// non-high-bandwidth endpoint (NBYTES=1023, bits [11:10]="00") to close
// usb_pie.m.vhdl lines 2632/2655/2680 - see that suite's README "LINE 2704
// IS NOT CLOSED BY THIS SUITE" note. Line 2704 (PID_DATA0 unexpected when
// iso_mdata_cnt_up /= "00") can only be reached on a HIGH-BANDWIDTH
// endpoint, since iso_mdata_cnt_up only increments on an accepted MDATA
// (usb_pie.m.vhdl incr_iso_mdata_cnt_up, ~line 2645), which itself requires
// iso_transact_cnt_down /= "00" at load time - the opposite endpoint
// configuration. Changing the existing suite's endpoint config in place
// would risk regressing its already-closed 2632/2655/2680 coverage, so per
// the "fork rather than risk" rule this is a new, standalone sibling test
// instead - no code in the original suite is touched.
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype bin pid_unknown (0x2), RTL site
// usb_pie.m.vhdl line 2704 (USB_PROT_OUT_SETUP_WF_RX_DATA_PID, the
// "iso_out_pending_r = '1'" case statement, PID_DATA0 branch, taken when
// "iso_mdata_cnt_up /= 00"). This test adds no new BIN coverage (pid_unknown
// is already closed by the sibling suite); its only purpose is the RTL
// line/branch hit at 2704.
//
// WHY THE FIRST DATA PHASE MUST BE A LEGITIMATE MDATA
//
// iso_mdata_cnt_up starts at "00" on a fresh transfer and only increments on
// an ACCEPTED MDATA (incr_iso_mdata_cnt_up). So reaching line 2704's guard
// ("iso_mdata_cnt_up /= 00") requires a first, legitimate MDATA data phase
// to be accepted before the mismatching DATA0 is sent. On this
// high-bandwidth endpoint (NBYTES bits [11:10]="10", loaded by the firmware
// - see caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw.c), that first MDATA is
// legal and IS accepted (usb_pie.m.vhdl line 2632's guard,
// "iso_transact_cnt_down = 00 or iso_mdata_cnt_up = 10", is false on the
// first packet), so it reaches the normal DMA handoff and the firmware sees
// one EP2 OUT completion for it.
//
// WHY A DIRECTED PACKET SEQUENCE, NOT THE TRANSFER SEQUENCER
//
// Same reasoning as the non-HBW sibling: the VIP's svt_usb_transfer API only
// emits MDATA when isoc_mult is configured for true high-bandwidth
// operation end-to-end (src/usb/tb/sequences/usb_high_bandwidth_iso_seq.svh),
// and it has no way to send a bare DATA0 packet out of sequence at all. Both
// data phases in this sequence are therefore driven directly on the packet
// sequencer via caliptra_ss_usb_err_inject_packet_sequence, each preceded by
// its own directed OUT token (same pattern as
// caliptra_ss_usb_hs_dev_err_iso_pid_seq_sequence's send_mismatched_data_pid()).
//
// NO EXCEPTION IS INJECTED
//
// DATA0 is a real, well formed PID - the error is purely sequencing (this
// endpoint expects MDATA or DATA2 next, not DATA0), the same "sequencing
// error" category as the non-HBW sibling. attach_exception stays cleared on
// every packet.
//
// NO HANDSHAKE IS EXPECTED FOR THE MISMATCHING PACKET
//
// Isochronous transfers never carry a handshake (USB 2.0 section 8.5.5), and
// line 2704's branch additionally clears the ISO pending flags and returns
// the FSM to WF_IDLE without reaching a DMA/ACK step, so the mismatching
// DATA0 packet is never answered.
// =============================================================================

class caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw_sequence
    extends caliptra_ss_usb_err_inject_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw_sequence)

    string MSG_ID = "USB_ERR_ISO_PID_SEQ_HBW";

    // Same EP2 ISO OUT slot/anchor convention as the non-HBW sibling suite.
    localparam int EP2_ISO    = 2;
    localparam int EP2_ANCHOR = 2;

    // Bound on how long to wait for each data phase to (not) complete. Same
    // style/value as the non-HBW sibling's MDATA_RESPONSE_BOUND.
    localparam realtime DATA_RESPONSE_BOUND = 200us;

    function new(string name = "caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw_sequence");
        super.new(name);
        inject_on_label = "";
    endfunction

    // Sends a directed OUT token followed by a bare data packet carrying the
    // given PID, no exception attached. Bounded the same way as
    // inject_error_packet()'s fork - the DUT may not answer either packet.
    protected task send_data_phase(svt_usb_configuration         usb_cfg,
                                    svt_usb_packet::pid_name_enum pid,
                                    string                        label);
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
            $sformatf("[%s] Sending a directed OUT token to addr %0d ep %0d so the PIE is in its data phase.",
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
            $sformatf("[%s] Sending %s to addr %0d ep %0d.",
                      label, pid.name(), USBDC0_ADDR, EP2_ISO), UVM_LOW)

        sent = 1'b0;
        fork : bounded_data_phase
            begin
                data_seq.start(p_sequencer.usb_20_pkt_sequencer);
                sent = 1'b1;
            end
            begin
                #DATA_RESPONSE_BOUND;
            end
        join_any
        disable bounded_data_phase;

        if (!sent) begin
            data_seq.kill();
            `uvm_info(MSG_ID,
                $sformatf("[%s] %s packet did not complete within the response bound.",
                          label, pid.name()), UVM_LOW)
        end

        #ERROR_SETTLE_DELAY;
    endtask

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        bit                   ok;

        `uvm_info(MSG_ID,
            "Starting HBW out-of-sequence DATA0 scenario on EP2 isochronous OUT.",
            UVM_LOW)

        err_inject_bringup(host_agent_h, usb_cfg, MSG_ID, ok);
        if (!ok) return;

        // Phase 1: legitimate MDATA, legal as the first of up to 3 HBW
        // transactions on this endpoint. Accepted by the RTL - sets
        // iso_mdata_cnt_up to "01" (incr_iso_mdata_cnt_up) and reaches the
        // normal DMA handoff. This phase is the precondition for line 2704,
        // not itself a target.
        send_data_phase(usb_cfg, svt_usb_packet::MDATA, "PhaseMDATA_arm");

        // Phase 2: PID_DATA0 where MDATA/DATA1 is expected. Line 2704's
        // guard ("iso_mdata_cnt_up /= 00") is now true, so the RTL reports
        // pid_unknown and returns to WF_IDLE without a DMA step.
        send_data_phase(usb_cfg, svt_usb_packet::DATA0, "PhaseDATA0_mismatch");

        // Release the MCU. Same rationale as every other err-injection body
        // - see request_mcu_stop() in caliptra_ss_usb_err_inject_base_sequence.
        request_mcu_stop(MSG_ID);

        `uvm_info(MSG_ID,
            "HBW out-of-sequence DATA0 scenario complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_ERR_ISO_PID_SEQ_HBW_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
