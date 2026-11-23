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

`ifndef CALIPTRA_SS_USB_HS_DEV_ERR_PID_CHECK_DATA_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_ERR_PID_CHECK_DATA_SEQUENCE_SV

// =============================================================================
// PID check-field error injection on the DATA packet of a bulk OUT to USBDC0
// (High Speed).
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype, bin pid_encoding (0x1), RTL site
// usb_pie.m.vhdl line 2777 (bad PID check in the DATA PID of an OUT/SETUP
// data phase). caliptra_ss_usb_hs_dev_err_pid_check only corrupts the OUT
// TOKEN's PID (line 2130), so this is a different live site of the same
// errortype code.
//
// WHY A SEPARATE SEQUENCE INSTEAD OF EXTENDING THE PID SEQUENCE'S SELECTOR
//
// caliptra_ss_usb_hs_dev_err_pid_sequence already uses PID_CHECK_ERROR for
// the TOKEN carrier and ILLEGAL_DATA_PID_ERROR for the DATA carrier - adding
// a third combination (PID_CHECK_ERROR on DATA0) to that one class's
// pid_carrier_pid() selector would require a second enum or a bit, which is
// more invasive than a short, independent sequence that calls the same
// shared inject_error_packet() helper.
//
// inject_error_packet() already does the right thing for a DATA pid carrier:
// is_data_pkt is true for DATA0/DATA1, so it sends a directed, uncorrupted
// OUT token immediately before the corrupted DATA packet, putting the PIE in
// its data phase - see that helper's header for the measured evidence this
// is required.
// =============================================================================

class caliptra_ss_usb_hs_dev_err_pid_check_data_sequence
    extends caliptra_ss_usb_err_inject_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_err_pid_check_data_sequence)

    string MSG_ID = "USB_ERR_PID_CHECK_DATA";

    function new(string name = "caliptra_ss_usb_hs_dev_err_pid_check_data_sequence");
        super.new(name);
        inject_on_label = "HS_BULK_OUT_EP1_DATA_PID_CHECK_CORRUPT";
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        bit                   ok;

        `uvm_info(MSG_ID,
            "Starting PID check-field error injection on a DATA packet.",
            UVM_LOW)

        err_inject_bringup(host_agent_h, usb_cfg, MSG_ID, ok);
        if (!ok) return;

        do_clean_reference_xfer(host_agent_h, usb_cfg,
                                "HS_BULK_OUT_EP1_pre_clean", MSG_ID);

        // PID_CHECK_ERROR is self-contained (no sub-field). Carried on
        // DATA0: inject_error_packet() sends the preceding clean OUT token
        // automatically because is_data_pkt is true for this PID.
        inject_error_packet(
            .usb_cfg    (usb_cfg),
            .msg_id     (MSG_ID),
            .pid        (svt_usb_packet::DATA0),
            .byte_count (HS_BULK_MAX_PACKET),
            .kind       (svt_usb_packet_exception::PID_CHECK_ERROR),
            .use_crc    (1'b0),
            .crc_sel    (svt_usb_packet_exception::CRC16_ERROR),
            .use_phys   (1'b0),
            .phys_sel   (svt_usb_packet_exception::SYNC_ERROR),
            .use_len    (1'b0),
            .len_sel    (svt_usb_packet_exception::SHORT_PACKET_ERROR));

        do_clean_reference_xfer(host_agent_h, usb_cfg,
                                "HS_BULK_OUT_EP1_post_clean", MSG_ID);

        request_mcu_stop(MSG_ID);

        `uvm_info(MSG_ID,
            "PID check-field error injection (DATA packet) sequence complete.",
            UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_ERR_PID_CHECK_DATA_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
