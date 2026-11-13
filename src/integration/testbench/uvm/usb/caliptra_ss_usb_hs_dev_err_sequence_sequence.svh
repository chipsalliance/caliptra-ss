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

`ifndef CALIPTRA_SS_USB_HS_DEV_ERR_SEQUENCE_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_ERR_SEQUENCE_SEQUENCE_SV

// =============================================================================
// Transaction-sequencing error injection on USBDC0 bulk OUT (High Speed).
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype, bin wrong_data_toggle (0xF).
//
// THIS ONE NEEDS NO WIRE CORRUPTION AT ALL
//
// 0xF is ERROR_DATA_IGNORED_WRONG_DATA01, and its single live assignment is
// usb_pie.m.vhdl line 2917, on the else branch of the data-toggle comparison:
//
//     else
//       --SetError(ERROR_DATA_IGNORED_WRONG_DATA01);
//       errortype <= "1111"; --ERROR_DATA_IGNORED_WRONG_DATA01
//
// The device reaches it when the DATA PID it receives is not the one its
// endpoint toggle expects. USB 2.0 section 8.6 defines that case as a
// presumed retransmission: the device ACKs it but DISCARDS the payload,
// which is what "DATA_IGNORED" in the name records.
//
// So the stimulus is a sequencing manipulation, not a corruption, and it needs
// no exception at all: a plain, well formed DATA1 packet is driven directly on
// the packet sequencer. The clean reference transfer immediately before it
// leaves the endpoint expecting DATA0, so a DATA1 arrival is exactly the
// mismatch the comparison at line 2917 keys on.
//
// WHY NOT AN EXCEPTION (this was tried and the VIP rejects it)
//
// The first attempt expressed the skew as a PACKET_FIELD_ERROR on the PID_NAME
// field of a DATA0 carrier. The VIP's own legality constraint forbids that:
//
//   constraint valid_ranges  // svt_usb_packet_exception.svp:1523
//   {
//     ((!((xact.speed == SS) || (xact.speed == ESSG2))) &&
//      (xact.pid_type == DATA)) ->
//        (error_kind inside {CRC_ERROR, PHYSICAL_ERROR, ILLEGAL_DATA_PID_ERROR,
//                            PID_CHECK_ERROR, LENGTH_ERROR, NO_OP_ERROR});
//   }
//
// PACKET_FIELD_ERROR is not in that set, so pinning it against a USB 2.0 DATA
// packet is an unsatisfiable constraint and the solver fails. Sending the
// DATA1 packet as-is reaches the same device-side condition without needing an
// exception, so nothing is lost.
//
// WHY THE THIRD CLEAN TRANSFER MATTERS MORE HERE THAN ELSEWHERE
//
// Because the device ACKs the stale packet, the host believes the transfer
// succeeded while the device threw the data away. If the toggles then stayed
// out of step, every subsequent OUT would be discarded in the same way and
// the endpoint would be silently dead - the exact failure mode documented at
// length in do_data_xfer()'s dev_anchor_idx comment. The post-injection clean
// transfer is therefore the check that the toggle re-synchronised.
//
// ASSUMPTION, STATED EXPLICITLY
//
// Driving the packet on the packet sequencer bypasses the transfer layer, so
// the VIP's own per-endpoint toggle tracking does not rewrite the PID - the
// same property caliptra_ss_usb_ocp_directed_packet_sequence relies on to emit
// explicit DATA0/DATA1 packets. What cannot be confirmed from documentation
// alone is whether the hub forwards an out-of-turn DATA packet that is not
// preceded by its own OUT token in the same microframe. If the first run shows
// the bin still open, the next step is to precede the DATA1 with a directed OUT
// token to the same address and endpoint so the PIE is in its data phase when
// the DATA1 arrives.
// =============================================================================

class caliptra_ss_usb_hs_dev_err_sequence_sequence
    extends caliptra_ss_usb_err_inject_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_err_sequence_sequence)

    string MSG_ID = "USB_ERR_SEQ";

    function new(string name = "caliptra_ss_usb_hs_dev_err_sequence_sequence");
        super.new(name);
        inject_on_label = "HS_BULK_OUT_EP1_TOGGLE_SKEW";
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        bit                   ok;

        `uvm_info(MSG_ID,
            "Starting data-toggle sequencing error injection.", UVM_LOW)

        err_inject_bringup(host_agent_h, usb_cfg, MSG_ID, ok);
        if (!ok) return;

        // Establishes the endpoint toggle at a known point before it is
        // deliberately skewed.
        do_clean_reference_xfer(host_agent_h, usb_cfg,
                                "HS_BULK_OUT_EP1_pre_clean", MSG_ID);

        // The skew itself: a well formed DATA1 packet with no exception
        // attached. The clean reference transfer above has just left the
        // endpoint expecting DATA0, so the device sees a DATA1 where it wanted
        // DATA0 - a toggle one step ahead - which is the condition for
        // ERROR_DATA_IGNORED_WRONG_DATA01 (0xF). kind is only carried for the
        // log message here; attach_exception == 0 means it is never applied.
        inject_error_packet(
            .usb_cfg          (usb_cfg),
            .msg_id           (MSG_ID),
            .pid              (svt_usb_packet::DATA1),
            .byte_count       (HS_BULK_MAX_PACKET),
            .kind             (svt_usb_packet_exception::NO_OP_ERROR),
            .use_crc          (1'b0),
            .crc_sel          (svt_usb_packet_exception::CRC16_ERROR),
            .use_phys         (1'b0),
            .phys_sel         (svt_usb_packet_exception::SYNC_ERROR),
            .use_len          (1'b0),
            .len_sel          (svt_usb_packet_exception::SHORT_PACKET_ERROR),
            .attach_exception (1'b0));

        // The toggle re-synchronisation check - see the header.
        do_clean_reference_xfer(host_agent_h, usb_cfg,
                                "HS_BULK_OUT_EP1_post_clean", MSG_ID);

        // Release the MCU. These firmware images have no completion event
        // of their own - a corrupted packet is meant to be discarded - so
        // without this they poll to USB_ERR_POLL_TIMEOUT and the simtime is
        // set by that loop count rather than by the stimulus. See
        // request_mcu_stop() in caliptra_ss_usb_err_inject_base_sequence.
        request_mcu_stop(MSG_ID);

        `uvm_info(MSG_ID,
            "Data-toggle sequencing error injection sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_ERR_SEQUENCE_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
