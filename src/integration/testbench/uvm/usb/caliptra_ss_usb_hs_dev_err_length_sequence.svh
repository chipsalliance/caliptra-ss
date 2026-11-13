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

`ifndef CALIPTRA_SS_USB_HS_DEV_ERR_LENGTH_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_ERR_LENGTH_SEQUENCE_SV

// =============================================================================
// Packet-length error injection on a bulk OUT to USBDC0 (High Speed).
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype, bins tr_eop (0x8) and overrun (0xB).
//
// WHY A LENGTH ERROR PRODUCES THESE TWO CODES
//
//   0x8 ERROR_TR_EOP - 4 live sites in usb_pie.m.vhdl. The packet ends where
//       the receiver was not expecting an end of packet. Injected with
//       length_error == SHORT_PACKET_ERROR, documented in the VIP reference
//       as "used by 2.0. The length of the data packet is shortened by N
//       number of bytes (byte_offset). The payload is shortened first with
//       CRC16 calculated for the shortened payload" - so the packet is
//       internally consistent but ends early, which is exactly a premature
//       EOP rather than a CRC failure.
//
//   0xB ERROR_OVERRUN - 2 live sites. More data arrived than the endpoint
//       buffer could take. Injected with length_error == LONG_PACKET_ERROR,
//       "the length of the data packet is elongated with bogus data by N
//       number of bytes". The base class sends exactly one HS bulk max
//       packet (512 B), so any elongation pushes the packet past
//       wMaxPacketSize and into the overrun path.
//
// Both are length_error_enum members and therefore need
// error_kind == LENGTH_ERROR; neither is an error_kind in its own right.
//
// WHY byte_offset IS PINNED
//
// byte_offset selects how many bytes are added or removed, and the VIP's
// valid_ranges constraint only bounds it as >= 0
// (sverilog/src/com/svt_usb_packet_exception.svp:1885). An unpinned solve may
// therefore legally choose 0, which leaves the packet the correct length and
// injects nothing - the test would pass while covering nothing. It is supplied
// explicitly through length_delta_bytes below.
// =============================================================================

class caliptra_ss_usb_hs_dev_err_length_sequence
    extends caliptra_ss_usb_err_inject_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_err_length_sequence)

    string MSG_ID = "USB_ERR_LENGTH";

    // SHORT_PACKET_ERROR -> errortype 0x8, LONG_PACKET_ERROR -> 0xB.
    svt_usb_packet_exception::length_error_enum length_target =
        svt_usb_packet_exception::SHORT_PACKET_ERROR;

    // How many bytes the packet is shortened or elongated by. The VIP only
    // constrains byte_offset as >= 0, so leaving it to the solver can produce
    // 0 and a correctly sized packet; it has to be pinned. 4 is chosen so a
    // SHORT_PACKET_ERROR truncates inside the payload rather than eating the
    // CRC16 and PID bytes, and so a LONG_PACKET_ERROR clears wMaxPacketSize by
    // a whole word.
    int unsigned length_delta_bytes = 4;

    function new(string name = "caliptra_ss_usb_hs_dev_err_length_sequence");
        super.new(name);
        inject_on_label = "HS_BULK_OUT_EP1_LENGTH_CORRUPT";
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        bit                   ok;

        `uvm_info(MSG_ID,
            $sformatf("Starting length error injection, length_error=%s.",
                      length_target.name()), UVM_LOW)

        err_inject_bringup(host_agent_h, usb_cfg, MSG_ID, ok);
        if (!ok) return;

        do_clean_reference_xfer(host_agent_h, usb_cfg,
                                "HS_BULK_OUT_EP1_pre_clean", MSG_ID);

        // A length error only means anything on a DATA packet - a token has a
        // fixed length by definition. The payload is exactly one HS bulk max
        // packet so that LONG_PACKET_ERROR pushes it past wMaxPacketSize,
        // which is the condition the overrun path keys on.
        //
        // The injected packet must be sent as DATA1, not DATA0: the preceding
        // do_clean_reference_xfer() above already completes one clean DATA0
        // bulk OUT transfer, so the endpoint's data toggle next expects
        // DATA1. Sending DATA0 here creates a toggle mismatch, which makes
        // the RTL discard the packet via ignore_data_r before it ever
        // reaches the length/overrun check - the PIE reports
        // DATA_IGNORED_WRONG_DATA01 (0xF) instead of TR_EOP/OVERRUN.
        inject_error_packet(
            .usb_cfg         (usb_cfg),
            .msg_id          (MSG_ID),
            .pid             (svt_usb_packet::DATA1),
            .byte_count      (HS_BULK_MAX_PACKET),
            .kind            (svt_usb_packet_exception::LENGTH_ERROR),
            .use_crc         (1'b0),
            .crc_sel         (svt_usb_packet_exception::CRC16_ERROR),
            .use_phys        (1'b0),
            .phys_sel        (svt_usb_packet_exception::SYNC_ERROR),
            .use_len         (1'b1),
            .len_sel         (length_target),
            .len_byte_offset (length_delta_bytes));

        do_clean_reference_xfer(host_agent_h, usb_cfg,
                                "HS_BULK_OUT_EP1_post_clean", MSG_ID);

        // Release the MCU. These firmware images have no completion event
        // of their own - a corrupted packet is meant to be discarded - so
        // without this they poll to USB_ERR_POLL_TIMEOUT and the simtime is
        // set by that loop count rather than by the stimulus. See
        // request_mcu_stop() in caliptra_ss_usb_err_inject_base_sequence.
        request_mcu_stop(MSG_ID);

        `uvm_info(MSG_ID, "Length error injection sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_ERR_LENGTH_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
