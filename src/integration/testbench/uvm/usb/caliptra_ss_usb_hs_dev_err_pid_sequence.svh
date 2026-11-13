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

`ifndef CALIPTRA_SS_USB_HS_DEV_ERR_PID_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_ERR_PID_SEQUENCE_SV

// =============================================================================
// PID error injection on a bulk OUT to USBDC0 (High Speed).
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype, bins pid_encoding (0x1) and
// pid_unknown (0x2).
//
// THE TWO ERRORS ARE GENUINELY DIFFERENT RTL PATHS
//
// Both are driven from usb_pie.m.vhdl and they are not interchangeable:
//
//   0x1 ERROR_PID_ENCODING - 4 live sites. The PID byte's check field does
//       not match its type field. A USB 2.0 PID byte carries the 4-bit PID
//       in the low nibble and its ones-complement in the high nibble
//       (section 8.3.1), so corrupting one nibble makes the byte
//       self-inconsistent and the receiver rejects it as a damaged PID
//       rather than as an unknown one. This is what PID_CHECK_ERROR injects.
//
//   0x2 ERROR_PID_UNKNOWN - 9 live sites, the most widely driven error code
//       in the PIE. The PID byte is internally CONSISTENT but names a packet
//       type the receiver does not accept in this context. That is what
//       ILLEGAL_DATA_PID_ERROR injects: a DATA PID that is not legal for the
//       endpoint type, documented in the VIP reference as "2.0 specific.
//       Injects DATA PID not legal for the endpoint type."
//
// So one is a corrupted PID and the other is a well-formed but wrong PID,
// which is why both bins exist and why one injection cannot close both.
//
// NOTE ON THE error_kind VALUES USED HERE
//
// PID_CHECK_ERROR and ILLEGAL_DATA_PID_ERROR are both top-level error_kind
// values in their own right - confirmed in the error_kind_enum listing of the
// packet-exception class reference, where they appear alongside CRC_ERROR and
// PHYSICAL_ERROR. They take no sub-field, unlike CRC_ERROR which needs
// crc_error, so inject_error_packet is called with all the sub-field selects
// cleared.
// =============================================================================

class caliptra_ss_usb_hs_dev_err_pid_sequence
    extends caliptra_ss_usb_err_inject_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_err_pid_sequence)

    string MSG_ID = "USB_ERR_PID";

    // Which PID fault this run injects. PID_CHECK_ERROR -> errortype 0x1,
    // ILLEGAL_DATA_PID_ERROR -> errortype 0x2. Set from the test.
    svt_usb_packet_exception::error_kind_enum pid_error_kind =
        svt_usb_packet_exception::PID_CHECK_ERROR;

    function new(string name = "caliptra_ss_usb_hs_dev_err_pid_sequence");
        super.new(name);
        inject_on_label = "HS_BULK_OUT_EP1_PID_CORRUPT";
    endfunction

    // Which packet the bad PID rides on.
    //
    // PID_CHECK_ERROR corrupts the PID check-field, which every packet has, so
    // the OUT token is used - that is the first packet of the transaction and
    // the PIE decodes it before anything else, giving the cleanest attribution.
    // ILLEGAL_DATA_PID_ERROR is by definition about a DATA packet PID, so that
    // one targets DATA0.
    protected function svt_usb_packet::pid_name_enum pid_carrier_pid();
        if (pid_error_kind == svt_usb_packet_exception::ILLEGAL_DATA_PID_ERROR)
            return svt_usb_packet::DATA0;
        return svt_usb_packet::OUT;
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        bit                   ok;

        `uvm_info(MSG_ID,
            $sformatf("Starting PID error injection, error_kind=%s.",
                      pid_error_kind.name()), UVM_LOW)

        err_inject_bringup(host_agent_h, usb_cfg, MSG_ID, ok);
        if (!ok) return;

        do_clean_reference_xfer(host_agent_h, usb_cfg,
                                "HS_BULK_OUT_EP1_pre_clean", MSG_ID);

        // No sub-field: these two error_kind values are self-contained.
        inject_error_packet(
            .usb_cfg    (usb_cfg),
            .msg_id     (MSG_ID),
            .pid        (pid_carrier_pid()),
            .byte_count (HS_BULK_MAX_PACKET),
            .kind       (pid_error_kind),
            .use_crc    (1'b0),
            .crc_sel    (svt_usb_packet_exception::CRC16_ERROR),
            .use_phys   (1'b0),
            .phys_sel   (svt_usb_packet_exception::SYNC_ERROR),
            .use_len    (1'b0),
            .len_sel    (svt_usb_packet_exception::SHORT_PACKET_ERROR));

        do_clean_reference_xfer(host_agent_h, usb_cfg,
                                "HS_BULK_OUT_EP1_post_clean", MSG_ID);

        // Release the MCU. These firmware images have no completion event
        // of their own - a corrupted packet is meant to be discarded - so
        // without this they poll to USB_ERR_POLL_TIMEOUT and the simtime is
        // set by that loop count rather than by the stimulus. See
        // request_mcu_stop() in caliptra_ss_usb_err_inject_base_sequence.
        request_mcu_stop(MSG_ID);

        `uvm_info(MSG_ID, "PID error injection sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_ERR_PID_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
