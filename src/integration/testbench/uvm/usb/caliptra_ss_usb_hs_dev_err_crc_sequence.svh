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

`ifndef CALIPTRA_SS_USB_HS_DEV_ERR_CRC_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_ERR_CRC_SEQUENCE_SV

// =============================================================================
// CRC error injection on a bulk OUT to USBDC0 (High Speed).
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype, bins data_crc (0x5) and token_crc
// (0x4). Both were at zero: nothing in the regression corrupted a CRC.
//
// WHAT THE RTL DOES WITH A BAD CRC
//
// data_crc (0x5) has exactly ONE assignment site in the whole PIE,
// usb_pie.m.vhdl line 2953, on the else branch of the CRC16 check:
//
//     else  --  BAD CRC: Data Packet Corrupted , no  hanshake is returned
//        errortype <= "0101"; --ERROR_DATA_CRC
//
// That comment is the reason this test does not assert transfer success on
// the corrupted leg. The device returns NO HANDSHAKE at all, so from the
// host's point of view the transfer simply never completes: the VIP reports
// ABORTED or hits its response timeout. That is the correct device behaviour
// per USB 2.0 section 8.7.1 (a data packet with a bad CRC is discarded
// silently, so the host retries), not a failure of this test.
//
// token_crc (0x4) is the CRC5 field of the token packet rather than the CRC16
// of the data packet, and has two assignment sites.
//
// WHY TWO LEGS, AND WHY THE CLEAN ONES
//
// Step 2 is a clean transfer. Without it, a run where EP1 was never armed at
// all would produce no error bin either, and the two cases would be
// indistinguishable in the coverage report. Step 4 is also clean and is the
// more important of the two: it proves the endpoint RECOVERED from the error
// rather than wedging. An error-injection test that only injects tells you
// the error was detected but not that the device survived it.
// =============================================================================

class caliptra_ss_usb_hs_dev_err_crc_sequence
    extends caliptra_ss_usb_err_inject_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_err_crc_sequence)

    string MSG_ID = "USB_ERR_CRC";

    // Which CRC field this run corrupts. CRC16_ERROR targets the data
    // packet's CRC16 (-> errortype 0x5), CRC5_ERROR the token's CRC5
    // (-> errortype 0x4). Settable from the test so the two bins can be
    // closed by two runs of one sequence rather than two near-identical
    // sequence files.
    svt_usb_packet_exception::crc_error_enum crc_target =
        svt_usb_packet_exception::CRC16_ERROR;

    function new(string name = "caliptra_ss_usb_hs_dev_err_crc_sequence");
        super.new(name);
        inject_on_label = "HS_BULK_OUT_EP1_CRC_CORRUPT";
    endfunction

    // Which packet carries the corrupted CRC.
    //
    // CRC5 lives in the TOKEN packet and CRC16 in the DATA packet, so the two
    // bins need two different packets - corrupting the CRC16 of an OUT token
    // would be meaningless because a token has no CRC16 field at all.
    protected function svt_usb_packet::pid_name_enum crc_carrier_pid();
        if (crc_target == svt_usb_packet_exception::CRC5_ERROR)
            return svt_usb_packet::OUT;    // token, carries CRC5
        return svt_usb_packet::DATA0;      // data packet, carries CRC16
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        bit                   ok;

        `uvm_info(MSG_ID,
            $sformatf("Starting CRC error injection, crc_error=%s.",
                      crc_target.name()), UVM_LOW)

        // Step 1: link, SOF, enumerate hub then USBDC0 at address 2.
        err_inject_bringup(host_agent_h, usb_cfg, MSG_ID, ok);
        if (!ok) return;

        // Step 2: clean bulk OUT, establishing that EP1 works.
        do_clean_reference_xfer(host_agent_h, usb_cfg,
                                "HS_BULK_OUT_EP1_pre_clean", MSG_ID);

        // Step 3: the corrupted packet. Expected to fail on the bus; see the
        // header. Injection is done at packet level because that is the only
        // layer svt_usb_packet_exception can attach to - see the note in
        // caliptra_ss_usb_err_inject_base_sequence.
        inject_error_packet(
            .usb_cfg    (usb_cfg),
            .msg_id     (MSG_ID),
            .pid        (crc_carrier_pid()),
            .byte_count (HS_BULK_MAX_PACKET),
            .kind       (svt_usb_packet_exception::CRC_ERROR),
            .use_crc    (1'b1),
            .crc_sel    (crc_target),
            .use_phys   (1'b0),
            .phys_sel   (svt_usb_packet_exception::SYNC_ERROR),
            .use_len    (1'b0),
            .len_sel    (svt_usb_packet_exception::SHORT_PACKET_ERROR));

        // Step 4: clean bulk OUT again - the recovery check.
        do_clean_reference_xfer(host_agent_h, usb_cfg,
                                "HS_BULK_OUT_EP1_post_clean", MSG_ID);

        // Release the MCU. These firmware images have no completion event
        // of their own - a corrupted packet is meant to be discarded - so
        // without this they poll to USB_ERR_POLL_TIMEOUT and the simtime is
        // set by that loop count rather than by the stimulus. See
        // request_mcu_stop() in caliptra_ss_usb_err_inject_base_sequence.
        request_mcu_stop(MSG_ID);

        `uvm_info(MSG_ID, "CRC error injection sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_ERR_CRC_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
