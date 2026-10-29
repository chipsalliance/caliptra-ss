// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

`ifndef CALIPTRA_SS_USB_FS_DEV_ISO_OUT_SEQUENCE_SV
`define CALIPTRA_SS_USB_FS_DEV_ISO_OUT_SEQUENCE_SV

// =============================================================================
// USB Full-Speed device isochronous OUT + IN sequence.
//
// Sequence flow:
//   1. Wait for HS host link ENABLED (after HS chirp negotiation).
//   2. Start SOF generation.
//   3. Short settling delay for MCU firmware post-reset EP0 re-arm.
//   4. Enumerate DUT device (GET_DESC/GET_STATUS/SET_ADDRESS/GET_DESC/
//      GET_CONFIG/SET_CONFIG/GET_CONFIG_verify).
//   5-7 (repeated N_ISO_ROUNDS times):
//      5. Send 1024 bytes of isochronous OUT data to EP2 via HS.
//         Pattern per round r: byte[i] = (i + r*85) % 256.
//         HS ISO max packet size is 1024 bytes (USB 2.0 spec table 5-7).
//         Isochronous transfers carry no ACK/NAK handshake; data is committed
//         once per SOF interval and the host does not retry.
//      6. Allow MCU firmware time to verify received data and arm EP2 IN.
//      7. Receive 1024 bytes of isochronous IN data from EP2 via HS as
//         two separate 512-byte tokens (Buffer 0 then Buffer 1).
//         Pattern per round r: byte[i] = 255 - ((i + r*85) % 256).
//         Verify each received byte against expected pattern; report
//         UVM_ERROR on mismatch.
//
// Multiple rounds exercise: double-buffer re-arm, data-toggle sequencing,
// Active bit re-arm, stale-SRAM detection via varying patterns per round.
// =============================================================================

`define USB_FS_DEV_ISO_BYTES     1024
`define USB_FS_DEV_ISO_IN_BYTES   512
// Number of complete ISO OUT+IN round-trips to run.
// Inspired by usb2_iso_random_transfer reference test (count=10).
// 3 rounds verify double-buffer wrap-around and pattern variation within
// practical simulation time budgets.
`define N_ISO_ROUNDS              3
// Pattern base offset step between rounds (85 = 256/3, covers the full
// byte range across 3 rounds with no overlap in the repeating 256-period).
`define ISO_ROUND_OFFSET          8'd85

class caliptra_ss_usb_fs_dev_iso_out_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_fs_dev_iso_out_sequence)

    function new(string name = "caliptra_ss_usb_fs_dev_iso_out_sequence");
        super.new(name);
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;
        svt_usb_transfer      iso_req;
        svt_usb_transfer      iso_in_req0;
        svt_usb_transfer      iso_in_req1;
        bit [7:0]             iso_data[];
        int unsigned          iso_in_err_cnt;
        int unsigned          total_err_cnt;
        int unsigned          round;
        bit [7:0]             rnd_base;   // per-round pattern offset

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: Wait for HS link ENABLED.
        wait_for_link_enabled(shared_status, "HS host link");

        // Step 2: Start SOF generation.
        start_sof_generation();

        // Step 3: Settling delay for MCU firmware EP0 re-arm after bus reset.
        #20us;

        // Step 4: Enumerate the hub at address 1, bring up hub downstream
        // port 1, then enumerate USBDC0 at address 2 (base-class A -> B -> C).
        enumerate_hub_and_usbdc0(host_agent_h, usb_cfg);

        `uvm_info("USB_FS_DEV_ISO_SEQ", "HS enumeration complete.", UVM_LOW)
        #10us;


        // Steps 5-7: N_ISO_ROUNDS complete ISO OUT+IN round-trips.
        // Each round uses a different data pattern to verify that the DUT
        // returns freshly written SRAM data, not a stale previous buffer.
        // Pattern for round r: OUT byte[i] = (i + r*85) % 256 (ramp offset).
        //                      IN  byte[i] = 255 - ((i + r*85) % 256) (inverse).
        iso_data    = new[`USB_FS_DEV_ISO_BYTES];
        total_err_cnt = 0;

        for (round = 0; round < `N_ISO_ROUNDS; round++) begin

            rnd_base = 8'(`ISO_ROUND_OFFSET * round);

            `uvm_info("USB_FS_DEV_ISO_SEQ",
                $sformatf("--- ISO round %0d/%0d (pattern base=0x%02X) ---",
                          round, `N_ISO_ROUNDS - 1, rnd_base), UVM_LOW)

            // ----------------------------------------------------------------
            // Step 5: ISO OUT - 1024 bytes, pattern byte[i] = (i+rnd_base)%256.
            //
            // At full speed the VIP caps a single isochronous transaction at
            // SVT_USB_FS_ISOC_MAX_PACKET_SIZE (1023 bytes). Because
            // single_isoc_txn=1 forces last_isoc_transaction==1, requesting a
            // single 1024-byte FS ISO OUT transaction is an unsolvable
            // constraint in svt_usb_transfer.svp. Split the 1024-byte payload
            // into two 512-byte FS ISO OUT tokens (each <= 1023 bytes, legal),
            // mirroring the two-token IN side. Firmware accumulates both halves
            // into the same 1024-byte EP2 OUT buffer, so no firmware change is
            // required.
            // ----------------------------------------------------------------
            for (int unsigned i = 0; i < `USB_FS_DEV_ISO_BYTES; i++)
                iso_data[i] = 8'((i + rnd_base) % 256);

            begin
                bit [7:0] iso_data_h0[];
                bit [7:0] iso_data_h1[];
                iso_data_h0 = new[`USB_FS_DEV_ISO_IN_BYTES];
                iso_data_h1 = new[`USB_FS_DEV_ISO_IN_BYTES];
                for (int unsigned i = 0; i < `USB_FS_DEV_ISO_IN_BYTES; i++) begin
                    iso_data_h0[i] = iso_data[i];
                    iso_data_h1[i] = iso_data[i + `USB_FS_DEV_ISO_IN_BYTES];
                end

                // ISO OUT token 0 (bytes 0-511) via the base-class helper: it
                // forks the NOTIFY_USB_TRANSFER_ENDED wait before finish_item
                // (see do_data_xfer() in caliptra_ss_usb_base_sequence.svh).
                do_data_xfer(
                    .agent_h         (host_agent_h),
                    .usb_cfg         (usb_cfg),
                    .xfer_kind       (svt_usb_transfer::ISOCHRONOUS_OUT_TRANSFER),
                    .device_addr     (2),
                    .ep_num          (2),
                    .byte_count      (`USB_FS_DEV_ISO_IN_BYTES),
                    .ep_anchor_idx   (2),
                    .label           ($sformatf("FS_ISO_OUT_EP2_BUF0_r%0d", round)),
                    .req             (iso_req),
                    .obj_name        ($sformatf("iso_out_req0_r%0d", round)),
                    .payload_data    (iso_data_h0),
                    .single_isoc_txn (1));

                // One microframe gap before the second 512-byte OUT token.
                #125us;

                // ISO OUT token 1 (bytes 512-1023).
                do_data_xfer(
                    .agent_h         (host_agent_h),
                    .usb_cfg         (usb_cfg),
                    .xfer_kind       (svt_usb_transfer::ISOCHRONOUS_OUT_TRANSFER),
                    .device_addr     (2),
                    .ep_num          (2),
                    .byte_count      (`USB_FS_DEV_ISO_IN_BYTES),
                    .ep_anchor_idx   (2),
                    .label           ($sformatf("FS_ISO_OUT_EP2_BUF1_r%0d", round)),
                    .req             (iso_req),
                    .obj_name        ($sformatf("iso_out_req1_r%0d", round)),
                    .payload_data    (iso_data_h1),
                    .single_isoc_txn (1));
            end

            // ----------------------------------------------------------------
            // Step 6: Allow firmware time to verify OUT data and arm EP2 IN.
            // 100 us covers OUT data check (~48 us) + SRAM fill + EP list write.
            // ----------------------------------------------------------------
            #100us;

            // ----------------------------------------------------------------
            // Step 7a: ISO IN token 0 (Buffer 0, 512 bytes).
            // Expected: byte[i] = 255 - ((i + rnd_base) % 256).
            // ----------------------------------------------------------------
            `uvm_info("USB_FS_DEV_ISO_SEQ",
                $sformatf("ISO IN round %0d token 0 (512 B, BUF0)...", round),
                UVM_LOW)

            do_data_xfer(
                .agent_h         (host_agent_h),
                .usb_cfg         (usb_cfg),
                .xfer_kind       (svt_usb_transfer::ISOCHRONOUS_IN_TRANSFER),
                .device_addr     (2),
                .ep_num          (2),
                .byte_count      (`USB_FS_DEV_ISO_IN_BYTES),
                .ep_anchor_idx   (1),
                .label           ($sformatf("FS_ISO_IN_EP2_BUF0_r%0d", round)),
                .req             (iso_in_req0),
                .obj_name        ($sformatf("iso_in_req0_r%0d", round)),
                .single_isoc_txn (1));

            // One microframe gap before requesting the second 512-byte token.
            #125us;

            // ----------------------------------------------------------------
            // Step 7b: ISO IN token 1 (Buffer 1, 512 bytes).
            // ----------------------------------------------------------------
            `uvm_info("USB_FS_DEV_ISO_SEQ",
                $sformatf("ISO IN round %0d token 1 (512 B, BUF1)...", round),
                UVM_LOW)

            do_data_xfer(
                .agent_h         (host_agent_h),
                .usb_cfg         (usb_cfg),
                .xfer_kind       (svt_usb_transfer::ISOCHRONOUS_IN_TRANSFER),
                .device_addr     (2),
                .ep_num          (2),
                .byte_count      (`USB_FS_DEV_ISO_IN_BYTES),
                .ep_anchor_idx   (1),
                .label           ($sformatf("FS_ISO_IN_EP2_BUF1_r%0d", round)),
                .req             (iso_in_req1),
                .obj_name        ($sformatf("iso_in_req1_r%0d", round)),
                .single_isoc_txn (1));

            // ----------------------------------------------------------------
            // Data integrity check for this round.
            // BUF0: bytes 0-511,   expected = 255 - ((i + rnd_base) % 256).
            // BUF1: bytes 512-1023 same formula (pattern period = 256 bytes).
            // ----------------------------------------------------------------
            iso_in_err_cnt = 0;
            for (int unsigned ci = 0; ci < `USB_FS_DEV_ISO_IN_BYTES; ci++) begin
                bit [7:0] expected_val;
                expected_val = 8'(255 - ((ci + rnd_base) % 256));
                if (iso_in_req0.payload.data[ci] !== expected_val) begin
                    if (iso_in_err_cnt < 5)
                        `uvm_error("USB_FS_DEV_ISO_SEQ",
                            $sformatf(
                                "Round %0d BUF0 mismatch byte[%0d]: got 0x%02X exp 0x%02X",
                                round, ci, iso_in_req0.payload.data[ci], expected_val))
                    iso_in_err_cnt++;
                end
            end
            for (int unsigned ci = 0; ci < `USB_FS_DEV_ISO_IN_BYTES; ci++) begin
                bit [7:0] expected_val;
                expected_val = 8'(255 - ((ci + rnd_base) % 256));
                if (iso_in_req1.payload.data[ci] !== expected_val) begin
                    if (iso_in_err_cnt < 5)
                        `uvm_error("USB_FS_DEV_ISO_SEQ",
                            $sformatf(
                                "Round %0d BUF1 mismatch byte[%0d]: got 0x%02X exp 0x%02X",
                                round, ci, iso_in_req1.payload.data[ci], expected_val))
                    iso_in_err_cnt++;
                end
            end
            total_err_cnt += iso_in_err_cnt;
            if (iso_in_err_cnt == 0)
                `uvm_info("USB_FS_DEV_ISO_SEQ",
                    $sformatf("Round %0d ISO IN PASSED (%0d bytes verified).",
                              round, `USB_FS_DEV_ISO_BYTES), UVM_LOW)
            else
                `uvm_error("USB_FS_DEV_ISO_SEQ",
                    $sformatf("Round %0d ISO IN FAILED: %0d/%0d bytes mismatched.",
                              round, iso_in_err_cnt, `USB_FS_DEV_ISO_BYTES))

            // Inter-round gap: two microframes (250 us) - firmware pre-arms
            // EP2 OUT for the next round immediately after arming IN, so only
            // a short settling delay is needed before the next ISO OUT token.
            if (round < `N_ISO_ROUNDS - 1)
                #250us;

        end // for round

        // Final summary across all rounds.
        if (total_err_cnt == 0)
            `uvm_info("USB_FS_DEV_ISO_SEQ",
                $sformatf(
                    "ALL %0d ISO rounds PASSED (%0d bytes total verified).",
                    `N_ISO_ROUNDS,
                    `N_ISO_ROUNDS * `USB_FS_DEV_ISO_BYTES), UVM_LOW)
        else
            `uvm_error("USB_FS_DEV_ISO_SEQ",
                $sformatf("ISO test FAILED: %0d total byte mismatches across %0d rounds.",
                          total_err_cnt, `N_ISO_ROUNDS))

        // ----------------------------------------------------------------
        // FRAME_INT phase observation window.
        // After ISO rounds are done, firmware enables FRAME_INT_EN and counts
        // FRAME_INT (INTSTAT bit 30) events over ~2 ms (60000 iters at ~33
        // ns/iter), then verifies INTEN FRAME_INT_EN is cleared after disable.
        //
        // Timing: the sequence now reaches this point at ~2200 us (reduced
        // inter-round delays). Firmware finishes the FRAME_INT phase ~5300 us
        // after the sequence starts (~7500 us total). Hold 6000 us to ensure
        // the SV objection outlasts the firmware halt.
        // ----------------------------------------------------------------
        `uvm_info("USB_FS_DEV_ISO_SEQ",
            "All ISO rounds done. Holding 6000us for firmware FRAME_INT test phase...",
            UVM_LOW)
        #6000us;
        `uvm_info("USB_FS_DEV_ISO_SEQ",
            "FRAME_INT phase observation window elapsed.", UVM_LOW)

        `uvm_info("USB_FS_DEV_ISO_SEQ",
            "HS device isochronous OUT+IN sequence complete.", UVM_LOW)
    endtask

endclass

`undef USB_FS_DEV_ISO_BYTES
`undef USB_FS_DEV_ISO_IN_BYTES
`undef N_ISO_ROUNDS
`undef ISO_ROUND_OFFSET

`endif // CALIPTRA_SS_USB_FS_DEV_ISO_OUT_SEQUENCE_SV
