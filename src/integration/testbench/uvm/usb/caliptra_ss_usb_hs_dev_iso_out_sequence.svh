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

`ifndef CALIPTRA_SS_USB_HS_DEV_ISO_OUT_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_ISO_OUT_SEQUENCE_SV

// =============================================================================
// USB High-Speed device isochronous OUT + IN sequence.
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

`define USB_HS_DEV_ISO_BYTES     1024
`define USB_HS_DEV_ISO_IN_BYTES   512
// Number of complete ISO OUT+IN round-trips to run.
// Inspired by usb2_iso_random_transfer reference test (count=10).
// 3 rounds verify double-buffer wrap-around and pattern variation within
// practical simulation time budgets.
`define N_ISO_ROUNDS              3
// Pattern base offset step between rounds (85 = 256/3, covers the full
// byte range across 3 rounds with no overlap in the repeating 256-period).
`define ISO_ROUND_OFFSET          8'd85

class caliptra_ss_usb_hs_dev_iso_out_sequence extends uvm_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_iso_out_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_hs_dev_iso_out_sequence");
        super.new(name);
    endfunction

    virtual task pre_start();
        uvm_phase phase;
        super.pre_start();
        phase = get_starting_phase();
        if (get_parent_sequence() == null && phase != null)
            phase.raise_objection(this);
    endtask

    virtual task post_start();
        uvm_phase phase;
        phase = get_starting_phase();
        if (get_parent_sequence() == null && phase != null)
            phase.drop_objection(this);
    endtask

    // -------------------------------------------------------------------------
    // Helper: issue a single CONTROL transfer.
    // Mirrors caliptra_ss_usb_hs_dev_bulk_out_sequence: finish_item only inside
    // this task, no NOTIFY wait. The caller calls wait_xfer_done() afterwards.
    // -------------------------------------------------------------------------
    task do_control_xfer(
        input bit [7:0]  bm_request_type_dir,
        input bit [7:0]  bm_request_type_type,
        input bit [7:0]  bm_request_type_recip,
        input bit [7:0]  brequest_val,
        input bit [15:0] wvalue,
        input bit [15:0] windex,
        input bit [15:0] wlength,
        input int        device_addr,
        input string     label,
        input svt_usb_configuration usb_cfg = null
    );
        svt_usb_transfer req;
        req = svt_usb_transfer::type_id::create({label, "_req"});
        start_item(req, -1, p_sequencer.xfer_sequencer);
        if (usb_cfg != null)
            req.cfg = usb_cfg;
        req.fix_anchors(0, 0, 0);
        if (!req.randomize() with {
                xfer_type                          == svt_usb_transfer::CONTROL_TRANSFER;
                device_address                     == device_addr;
                setup_data_bmrequesttype_dir       == bm_request_type_dir;
                setup_data_bmrequesttype_type      == bm_request_type_type;
                setup_data_bmrequesttype_recipient == bm_request_type_recip;
                setup_data_brequest                == brequest_val;
                setup_data_w_value                 == wvalue;
                setup_data_w_index                 == windex;
                setup_data_w_length                == wlength;
            }) begin
            `uvm_fatal("USB_HS_DEV_ISO_SEQ",
                $sformatf("randomize failed for %s", label))
        end
        finish_item(req, -1);
        `uvm_info("USB_HS_DEV_ISO_SEQ",
            $sformatf("CONTROL %s done (addr=%0d)", label, device_addr), UVM_LOW)
    endtask

    // -------------------------------------------------------------------------
    // Helper: wait for host-side transfer completion.
    // -------------------------------------------------------------------------
    task wait_xfer_done(svt_usb_agent agent_h, string label);
        agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
        `uvm_info("USB_HS_DEV_ISO_SEQ",
            $sformatf("Transfer %s completed.", label), UVM_LOW)
    endtask

    virtual task body();
        svt_usb_agent        host_agent_h;
        uvm_component        parent_comp;
        svt_configuration    get_cfg;
        svt_usb_configuration usb_cfg;
        svt_usb_status       shared_status;
        svt_usb_transfer     iso_req;
        svt_usb_transfer     iso_in_req0;
        svt_usb_transfer     iso_in_req1;
        bit [7:0]            iso_data[];
        int unsigned         iso_in_err_cnt;
        int unsigned         total_err_cnt;
        int unsigned         round;
        bit [7:0]            rnd_base;   // per-round pattern offset

        parent_comp = p_sequencer.get_parent();
        if (!$cast(host_agent_h, parent_comp))
            `uvm_fatal("USB_HS_DEV_ISO_SEQ",
                $sformatf("Cannot cast parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))

        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null)
            `uvm_fatal("USB_HS_DEV_ISO_SEQ", "get_shared_status returned null.")

        p_sequencer.get_cfg(get_cfg);
        if (!$cast(usb_cfg, get_cfg))
            `uvm_fatal("USB_HS_DEV_ISO_SEQ",
                "Unable to cast cfg to svt_usb_configuration")

        // Step 1: Wait for HS link ENABLED.
        `uvm_info("USB_HS_DEV_ISO_SEQ",
            $sformatf("Waiting for HS host link ENABLED (current=%p)...",
                      shared_status.link_usb_20_state), UVM_LOW)
        fork
            begin: WAIT_EN
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_LINK;
            end
            begin: REPORT_LINK
                forever begin
                    #10us `uvm_info("USB_HS_DEV_ISO_SEQ",
                        $sformatf("link_usb_20_state=%p",
                                  shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join
        `uvm_info("USB_HS_DEV_ISO_SEQ", "HS link ENABLED.", UVM_LOW)

        // Step 2: Start SOF generation.
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq;
            sof_on_seq = svt_usb_protocol_service_20_sof_on_sequence::type_id::create(
                "sof_on");
            sof_on_seq.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_HS_DEV_ISO_SEQ", "SOF started.", UVM_LOW)
        end

        // Step 3: Settling delay for MCU firmware EP0 re-arm after bus reset.
        #20us;

        // Step 4: Full HS device enumeration.
        // Pattern identical to caliptra_ss_usb_hs_dev_bulk_out_sequence:
        // do_control_xfer() issues finish_item; wait_xfer_done() waits for NOTIFY.
        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h0100, 16'h0000, 16'h0012,
            0, "GET_DESC_DEV_addr0", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_DESC_DEV_addr0");

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h00, 16'h0000, 16'h0000, 16'h0002,
            0, "GET_STATUS_addr0", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_STATUS_addr0");

        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h05, 16'h0001, 16'h0000, 16'h0000,
            0, "SET_ADDRESS_1", usb_cfg);
        wait_xfer_done(host_agent_h, "SET_ADDRESS_1");
        #5us;

        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h0100, 16'h0000, 16'h0012,
            1, "GET_DESC_DEV_addr1", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_DESC_DEV_addr1");

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h08, 16'h0000, 16'h0000, 16'h0001,
            1, "GET_CONFIG_addr1", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_CONFIG_addr1");

        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h09, 16'h0001, 16'h0000, 16'h0000,
            1, "SET_CONFIG_1", usb_cfg);
        wait_xfer_done(host_agent_h, "SET_CONFIG_1");

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h08, 16'h0000, 16'h0000, 16'h0001,
            1, "GET_CONFIG_verify", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_CONFIG_verify");

        `uvm_info("USB_HS_DEV_ISO_SEQ", "HS enumeration complete.", UVM_LOW)
        #10us;

        // Steps 5-7: N_ISO_ROUNDS complete ISO OUT+IN round-trips.
        // Each round uses a different data pattern to verify that the DUT
        // returns freshly written SRAM data, not a stale previous buffer.
        // Pattern for round r: OUT byte[i] = (i + r*85) % 256 (ramp offset).
        //                      IN  byte[i] = 255 - ((i + r*85) % 256) (inverse).
        iso_data    = new[`USB_HS_DEV_ISO_BYTES];
        total_err_cnt = 0;

        for (round = 0; round < `N_ISO_ROUNDS; round++) begin

            rnd_base = 8'(`ISO_ROUND_OFFSET * round);

            `uvm_info("USB_HS_DEV_ISO_SEQ",
                $sformatf("--- ISO round %0d/%0d (pattern base=0x%02X) ---",
                          round, `N_ISO_ROUNDS - 1, rnd_base), UVM_LOW)

            // ----------------------------------------------------------------
            // Step 5: ISO OUT — 1024 bytes, pattern byte[i] = (i+rnd_base)%256.
            // ----------------------------------------------------------------
            for (int unsigned i = 0; i < `USB_HS_DEV_ISO_BYTES; i++)
                iso_data[i] = 8'((i + rnd_base) % 256);

            iso_req = svt_usb_transfer::type_id::create(
                $sformatf("iso_out_req_r%0d", round));
            start_item(iso_req, -1, p_sequencer.xfer_sequencer);
            iso_req.cfg = usb_cfg;
            iso_req.payload.USER_DEFINED_ALGORITHM_wt   = 1;
            iso_req.payload.TWO_SEED_BASED_ALGORITHM_wt = 0;
            iso_req.fix_anchors(0, 2, 0);
            if (!iso_req.randomize() with {
                    xfer_type                   == svt_usb_transfer::ISOCHRONOUS_OUT_TRANSFER;
                    device_address              == 1;
                    endpoint_number             == 2;
                    payload_intended_byte_count == `USB_HS_DEV_ISO_BYTES;
                    first_isoc_transaction      == 1;
                    last_isoc_transaction       == 1;
                }) begin
                `uvm_fatal("USB_HS_DEV_ISO_SEQ",
                    $sformatf("ISO OUT randomize() failed (round %0d)", round))
            end
            for (int unsigned bi = 0; bi < `USB_HS_DEV_ISO_BYTES; bi++)
                iso_req.payload.data[bi] = iso_data[bi];

            // Fork NOTIFY wait before finish_item to avoid race with VIP.
            fork
                begin
                    finish_item(iso_req, -1);
                    `uvm_info("USB_HS_DEV_ISO_SEQ",
                        $sformatf("HS ISO OUT round %0d issued (1024 bytes, EP2).",
                                  round), UVM_LOW)
                end
                begin
                    wait_xfer_done(host_agent_h,
                        $sformatf("HS_ISO_OUT_EP2_r%0d", round));
                end
            join

            // ----------------------------------------------------------------
            // Step 6: Allow firmware time to verify OUT data and arm EP2 IN.
            // 500 us covers OUT data check (~48 us) + SRAM fill + EP list write.
            // ----------------------------------------------------------------
            #500us;

            // ----------------------------------------------------------------
            // Step 7a: ISO IN token 0 (Buffer 0, 512 bytes).
            // Expected: byte[i] = 255 - ((i + rnd_base) % 256).
            // ----------------------------------------------------------------
            `uvm_info("USB_HS_DEV_ISO_SEQ",
                $sformatf("ISO IN round %0d token 0 (512 B, BUF0)...", round),
                UVM_LOW)

            iso_in_req0 = svt_usb_transfer::type_id::create(
                $sformatf("iso_in_req0_r%0d", round));
            start_item(iso_in_req0, -1, p_sequencer.xfer_sequencer);
            iso_in_req0.cfg = usb_cfg;
            iso_in_req0.fix_anchors(0, 1, 0);
            if (!iso_in_req0.randomize() with {
                    xfer_type                   == svt_usb_transfer::ISOCHRONOUS_IN_TRANSFER;
                    device_address              == 1;
                    endpoint_number             == 2;
                    payload_intended_byte_count == `USB_HS_DEV_ISO_IN_BYTES;
                    first_isoc_transaction      == 1;
                    last_isoc_transaction       == 1;
                }) begin
                `uvm_fatal("USB_HS_DEV_ISO_SEQ",
                    $sformatf("ISO IN token 0 randomize() failed (round %0d)", round))
            end
            fork
                begin
                    finish_item(iso_in_req0, -1);
                    `uvm_info("USB_HS_DEV_ISO_SEQ",
                        $sformatf("ISO IN round %0d token 0 issued.", round), UVM_LOW)
                end
                begin
                    wait_xfer_done(host_agent_h,
                        $sformatf("HS_ISO_IN_EP2_BUF0_r%0d", round));
                end
            join

            // One microframe gap before requesting the second 512-byte token.
            #125us;

            // ----------------------------------------------------------------
            // Step 7b: ISO IN token 1 (Buffer 1, 512 bytes).
            // ----------------------------------------------------------------
            `uvm_info("USB_HS_DEV_ISO_SEQ",
                $sformatf("ISO IN round %0d token 1 (512 B, BUF1)...", round),
                UVM_LOW)

            iso_in_req1 = svt_usb_transfer::type_id::create(
                $sformatf("iso_in_req1_r%0d", round));
            start_item(iso_in_req1, -1, p_sequencer.xfer_sequencer);
            iso_in_req1.cfg = usb_cfg;
            iso_in_req1.fix_anchors(0, 1, 0);
            if (!iso_in_req1.randomize() with {
                    xfer_type                   == svt_usb_transfer::ISOCHRONOUS_IN_TRANSFER;
                    device_address              == 1;
                    endpoint_number             == 2;
                    payload_intended_byte_count == `USB_HS_DEV_ISO_IN_BYTES;
                    first_isoc_transaction      == 1;
                    last_isoc_transaction       == 1;
                }) begin
                `uvm_fatal("USB_HS_DEV_ISO_SEQ",
                    $sformatf("ISO IN token 1 randomize() failed (round %0d)", round))
            end
            fork
                begin
                    finish_item(iso_in_req1, -1);
                    `uvm_info("USB_HS_DEV_ISO_SEQ",
                        $sformatf("ISO IN round %0d token 1 issued.", round), UVM_LOW)
                end
                begin
                    wait_xfer_done(host_agent_h,
                        $sformatf("HS_ISO_IN_EP2_BUF1_r%0d", round));
                end
            join

            // ----------------------------------------------------------------
            // Data integrity check for this round.
            // BUF0: bytes 0-511,   expected = 255 - ((i + rnd_base) % 256).
            // BUF1: bytes 512-1023 same formula (pattern period = 256 bytes).
            // ----------------------------------------------------------------
            iso_in_err_cnt = 0;
            for (int unsigned ci = 0; ci < `USB_HS_DEV_ISO_IN_BYTES; ci++) begin
                bit [7:0] expected_val;
                expected_val = 8'(255 - ((ci + rnd_base) % 256));
                if (iso_in_req0.payload.data[ci] !== expected_val) begin
                    if (iso_in_err_cnt < 5)
                        `uvm_error("USB_HS_DEV_ISO_SEQ",
                            $sformatf(
                                "Round %0d BUF0 mismatch byte[%0d]: got 0x%02X exp 0x%02X",
                                round, ci, iso_in_req0.payload.data[ci], expected_val))
                    iso_in_err_cnt++;
                end
            end
            for (int unsigned ci = 0; ci < `USB_HS_DEV_ISO_IN_BYTES; ci++) begin
                bit [7:0] expected_val;
                expected_val = 8'(255 - ((ci + rnd_base) % 256));
                if (iso_in_req1.payload.data[ci] !== expected_val) begin
                    if (iso_in_err_cnt < 5)
                        `uvm_error("USB_HS_DEV_ISO_SEQ",
                            $sformatf(
                                "Round %0d BUF1 mismatch byte[%0d]: got 0x%02X exp 0x%02X",
                                round, ci, iso_in_req1.payload.data[ci], expected_val))
                    iso_in_err_cnt++;
                end
            end
            total_err_cnt += iso_in_err_cnt;
            if (iso_in_err_cnt == 0)
                `uvm_info("USB_HS_DEV_ISO_SEQ",
                    $sformatf("Round %0d ISO IN PASSED (%0d bytes verified).",
                              round, `USB_HS_DEV_ISO_BYTES), UVM_LOW)
            else
                `uvm_error("USB_HS_DEV_ISO_SEQ",
                    $sformatf("Round %0d ISO IN FAILED: %0d/%0d bytes mismatched.",
                              round, iso_in_err_cnt, `USB_HS_DEV_ISO_BYTES))

            // Inter-round gap: one full USB frame (1 ms) to allow firmware
            // to re-arm EP2 OUT for the next round.
            if (round < `N_ISO_ROUNDS - 1)
                #1000us;

        end // for round

        // Final summary across all rounds.
        if (total_err_cnt == 0)
            `uvm_info("USB_HS_DEV_ISO_SEQ",
                $sformatf(
                    "ALL %0d ISO rounds PASSED (%0d bytes total verified).",
                    `N_ISO_ROUNDS,
                    `N_ISO_ROUNDS * `USB_HS_DEV_ISO_BYTES), UVM_LOW)
        else
            `uvm_error("USB_HS_DEV_ISO_SEQ",
                $sformatf("ISO test FAILED: %0d total byte mismatches across %0d rounds.",
                          total_err_cnt, `N_ISO_ROUNDS))

        // ----------------------------------------------------------------
        // FRAME_INT phase observation window.
        // After ISO rounds are done, firmware enables FRAME_INT_EN and counts
        // FRAME_INT (INTSTAT bit 30) events over ~2 ms (60000 iters at ~33
        // ns/iter), then verifies INTEN FRAME_INT_EN is cleared after disable.
        //
        // Timing (measured):
        //   ~4340 us: sequence reaches this point (after ISO round 2 summary)
        //   ~7504 us: firmware halts
        //   Target SV end: ~7504 + 300 = ~7804 us
        //   Hold needed: 7804 - 4340 = ~3464 us -> use 3400 us (measured ok).
        // ----------------------------------------------------------------
        `uvm_info("USB_HS_DEV_ISO_SEQ",
            "All ISO rounds done. Holding 3400us for firmware FRAME_INT test phase...",
            UVM_LOW)
        #3400us;
        `uvm_info("USB_HS_DEV_ISO_SEQ",
            "FRAME_INT phase observation window elapsed.", UVM_LOW)

        `uvm_info("USB_HS_DEV_ISO_SEQ",
            "HS device isochronous OUT+IN sequence complete.", UVM_LOW)
    endtask

endclass

`undef USB_HS_DEV_ISO_BYTES
`undef USB_HS_DEV_ISO_IN_BYTES
`undef N_ISO_ROUNDS
`undef ISO_ROUND_OFFSET

`endif // CALIPTRA_SS_USB_HS_DEV_ISO_OUT_SEQUENCE_SV
