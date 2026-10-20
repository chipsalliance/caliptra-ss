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

`ifndef CALIPTRA_SS_USB_HS_DEV_INT_ISO_MIX_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_INT_ISO_MIX_SEQUENCE_SV

// =============================================================================
// USB High-Speed device mixed INTERRUPT (EP1) + ISOCHRONOUS (EP2) +
// INTERRUPT (EP3) sequence.
//
// This sequence merges caliptra_ss_usb_hs_dev_int_loopback_sequence (INTERRUPT
// OUT + IN loopback) and caliptra_ss_usb_hs_dev_iso_out_sequence (ISO OUT 1024
// bytes + two 512-byte ISO IN tokens) into a single simulation so that both
// endpoint types are armed at the same time and the shared device DMA / EP
// command-status list is exercised concurrently.
//
// Endpoint access order (as requested): EP1 -> EP2 -> EP3
//   Phase 0: EP1 INTERRUPT OUT 64 B, pattern byte[i] = i, then INTERRUPT
//            IN 64 B from EP1 and byte-compare (firmware loops OUT -> IN).
//   Phase 1: EP2 ISOCHRONOUS OUT 1024 B, pattern byte[i] = i % 256, then
//            two ISOCHRONOUS IN tokens of 512 B each from EP2, expected
//            byte[i] = 255 - (i % 256).
//   Phase 2: EP3 INTERRUPT OUT 64 B + IN 64 B loopback, identical mechanism to
//            phase 0 but on a SECOND interrupt endpoint and with a shifted
//            pattern byte[i] = (i + 85) % 256. The distinct endpoint proves
//            the EP command/status list indexing is correct for a third live
//            endpoint, and the distinct pattern proves no stale SRAM from
//            phase 0 is returned.
//
// Endpoint assignment is FIXED (no randomization, no reconfigure()):
//   EP1 = INTERRUPT, EP2 = ISOCHRONOUS, EP3 = INTERRUPT. These must match
//   USB_INT_EP / USB_ISO_EP / USB_INT_EP2 in
//   caliptra_ss_usb_hs_dev_int_iso_mix.c and the endpoint_cfg[] slots built by
//   caliptra_ss_usb_hs_dev_int_iso_mix_test.
//
// endpoint_cfg[] slot map (array index, NOT endpoint number):
//   [0] EP0 CONTROL   [1] EP2 ISO IN   [2] EP2 ISO OUT
//   [3] EP1 INT IN    [4] EP1 INT OUT
//   [5] EP3 INT IN    [6] EP3 INT OUT
// =============================================================================

class caliptra_ss_usb_hs_dev_int_iso_mix_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_int_iso_mix_sequence)

    // Endpoint numbers - must match the firmware.
    localparam int INT_EP            = 1;
    localparam int ISO_EP            = 2;
    localparam int INT_EP2           = 3;

    // Transfer sizes.
    localparam int INT_XFER_BYTES    = 64;
    localparam int ISO_BYTES         = 1024;
    localparam int ISO_IN_BYTES      = 512;

    // Pattern offset applied on the second INTERRUPT endpoint (EP3).
    localparam int INT_ROUND_OFFSET  = 85;

    // endpoint_cfg[] array indices.
    localparam int ISO_IN_ANCHOR     = 1;
    localparam int ISO_OUT_ANCHOR    = 2;
    localparam int INT_IN_ANCHOR     = 3;
    localparam int INT_OUT_ANCHOR    = 4;
    localparam int INT2_IN_ANCHOR    = 5;
    localparam int INT2_OUT_ANCHOR   = 6;

    function new(string name = "caliptra_ss_usb_hs_dev_int_iso_mix_sequence");
        super.new(name);
    endfunction

    // -------------------------------------------------------------------------
    // One INTERRUPT OUT + IN loopback round on an arbitrary interrupt endpoint.
    // Pattern: byte[i] = (i + pattern_base) % 256.
    // -------------------------------------------------------------------------
    virtual task run_int_round(svt_usb_agent         host_agent_h,
                               svt_usb_configuration usb_cfg,
                               int unsigned          ep_num,
                               int unsigned          out_anchor,
                               int unsigned          in_anchor,
                               int unsigned          pattern_base,
                               ref int unsigned      err_cnt);
        svt_usb_transfer int_out_req;
        svt_usb_transfer int_in_req;
        bit [7:0]        send_data[];
        bit [7:0]        rnd_base;
        int unsigned     mismatch_count;

        rnd_base  = 8'(pattern_base % 256);
        send_data = new[INT_XFER_BYTES];
        for (int unsigned i = 0; i < INT_XFER_BYTES; i++)
            send_data[i] = 8'((i + rnd_base) % 256);

        `uvm_info("USB_HS_INT_ISO_MIX_SEQ",
            $sformatf("--- INTERRUPT round on EP%0d (pattern base=0x%02X) ---",
                      ep_num, rnd_base), UVM_LOW)

        do_data_xfer(
            .agent_h       (host_agent_h),
            .usb_cfg       (usb_cfg),
            .xfer_kind     (svt_usb_transfer::INTERRUPT_OUT_TRANSFER),
            .device_addr   (2),
            .ep_num        (ep_num),
            .byte_count    (INT_XFER_BYTES),
            .ep_anchor_idx (out_anchor),
            .label         ($sformatf("HS_INT_OUT_EP%0d", ep_num)),
            .req           (int_out_req),
            .obj_name      ($sformatf("int_out_req_ep%0d", ep_num)),
            .payload_data  (send_data));

        // Allow firmware to verify the OUT payload, copy it into the IN buffer
        // and arm the IN entry.
        #20us;

        do_data_xfer(
            .agent_h       (host_agent_h),
            .usb_cfg       (usb_cfg),
            .xfer_kind     (svt_usb_transfer::INTERRUPT_IN_TRANSFER),
            .device_addr   (2),
            .ep_num        (ep_num),
            .byte_count    (INT_XFER_BYTES),
            .ep_anchor_idx (in_anchor),
            .label         ($sformatf("HS_INT_IN_EP%0d", ep_num)),
            .req           (int_in_req),
            .obj_name      ($sformatf("int_in_req_ep%0d", ep_num)));

        mismatch_count = 0;
        for (int unsigned bi = 0; bi < INT_XFER_BYTES; bi++) begin
            if (int_in_req.payload.data[bi] !== send_data[bi]) begin
                if (mismatch_count < 5)
                    `uvm_error("USB_HS_INT_ISO_MIX_SEQ",
                        $sformatf("INT EP%0d mismatch byte[%0d]: sent=0x%02h got=0x%02h",
                                  ep_num, bi, send_data[bi], int_in_req.payload.data[bi]))
                mismatch_count++;
            end
        end
        err_cnt += mismatch_count;

        if (mismatch_count == 0)
            `uvm_info("USB_HS_INT_ISO_MIX_SEQ",
                $sformatf("INT EP%0d loopback PASSED (all %0d bytes match).",
                          ep_num, INT_XFER_BYTES), UVM_LOW)
        else
            `uvm_error("USB_HS_INT_ISO_MIX_SEQ",
                $sformatf("INT EP%0d loopback FAILED: %0d byte(s) mismatched.",
                          ep_num, mismatch_count))

        // Allow firmware to observe the IN Active-bit clear and re-arm.
        #20us;
    endtask

    // -------------------------------------------------------------------------
    // One ISOCHRONOUS OUT (1024 B) + two ISO IN (512 B) round on EP2.
    // OUT pattern byte[i] = i % 256, IN expected byte[i] = 255 - (i % 256).
    // -------------------------------------------------------------------------
    virtual task run_iso_round(svt_usb_agent         host_agent_h,
                               svt_usb_configuration usb_cfg,
                               ref int unsigned      err_cnt);
        svt_usb_transfer iso_out_req;
        svt_usb_transfer iso_in_req0;
        svt_usb_transfer iso_in_req1;
        bit [7:0]        iso_data[];
        int unsigned     iso_err_cnt;

        `uvm_info("USB_HS_INT_ISO_MIX_SEQ",
            $sformatf("--- ISOCHRONOUS round on EP%0d ---", ISO_EP), UVM_LOW)

        iso_data = new[ISO_BYTES];
        for (int unsigned i = 0; i < ISO_BYTES; i++)
            iso_data[i] = 8'(i % 256);

        do_data_xfer(
            .agent_h         (host_agent_h),
            .usb_cfg         (usb_cfg),
            .xfer_kind       (svt_usb_transfer::ISOCHRONOUS_OUT_TRANSFER),
            .device_addr     (2),
            .ep_num          (ISO_EP),
            .byte_count      (ISO_BYTES),
            .ep_anchor_idx   (ISO_OUT_ANCHOR),
            .label           ($sformatf("HS_ISO_OUT_EP%0d", ISO_EP)),
            .req             (iso_out_req),
            .obj_name        ("iso_out_req"),
            .payload_data    (iso_data),
            .single_isoc_txn (1));

        // Firmware verifies the OUT payload, fills the IN SRAM and arms both
        // IN buffer entries. 100 us covers the 1024-byte check plus the fill.
        #100us;

        `uvm_info("USB_HS_INT_ISO_MIX_SEQ",
            "ISO IN token 0 (512 B, BUF0)...", UVM_LOW)

        do_data_xfer(
            .agent_h         (host_agent_h),
            .usb_cfg         (usb_cfg),
            .xfer_kind       (svt_usb_transfer::ISOCHRONOUS_IN_TRANSFER),
            .device_addr     (2),
            .ep_num          (ISO_EP),
            .byte_count      (ISO_IN_BYTES),
            .ep_anchor_idx   (ISO_IN_ANCHOR),
            .label           ($sformatf("HS_ISO_IN_EP%0d_BUF0", ISO_EP)),
            .req             (iso_in_req0),
            .obj_name        ("iso_in_req0"),
            .single_isoc_txn (1));

        // One microframe gap before the second 512-byte token.
        #125us;

        `uvm_info("USB_HS_INT_ISO_MIX_SEQ",
            "ISO IN token 1 (512 B, BUF1)...", UVM_LOW)

        do_data_xfer(
            .agent_h         (host_agent_h),
            .usb_cfg         (usb_cfg),
            .xfer_kind       (svt_usb_transfer::ISOCHRONOUS_IN_TRANSFER),
            .device_addr     (2),
            .ep_num          (ISO_EP),
            .byte_count      (ISO_IN_BYTES),
            .ep_anchor_idx   (ISO_IN_ANCHOR),
            .label           ($sformatf("HS_ISO_IN_EP%0d_BUF1", ISO_EP)),
            .req             (iso_in_req1),
            .obj_name        ("iso_in_req1"),
            .single_isoc_txn (1));

        // BUF0 covers bytes 0-511 and BUF1 bytes 512-1023, but the pattern
        // period is 256 bytes so the expected formula is identical for both.
        iso_err_cnt = 0;
        for (int unsigned ci = 0; ci < ISO_IN_BYTES; ci++) begin
            bit [7:0] expected_val;
            expected_val = 8'(255 - (ci % 256));
            if (iso_in_req0.payload.data[ci] !== expected_val) begin
                if (iso_err_cnt < 5)
                    `uvm_error("USB_HS_INT_ISO_MIX_SEQ",
                        $sformatf("ISO BUF0 mismatch byte[%0d]: got 0x%02X exp 0x%02X",
                                  ci, iso_in_req0.payload.data[ci], expected_val))
                iso_err_cnt++;
            end
        end
        for (int unsigned ci = 0; ci < ISO_IN_BYTES; ci++) begin
            bit [7:0] expected_val;
            expected_val = 8'(255 - (ci % 256));
            if (iso_in_req1.payload.data[ci] !== expected_val) begin
                if (iso_err_cnt < 5)
                    `uvm_error("USB_HS_INT_ISO_MIX_SEQ",
                        $sformatf("ISO BUF1 mismatch byte[%0d]: got 0x%02X exp 0x%02X",
                                  ci, iso_in_req1.payload.data[ci], expected_val))
                iso_err_cnt++;
            end
        end
        err_cnt += iso_err_cnt;

        if (iso_err_cnt == 0)
            `uvm_info("USB_HS_INT_ISO_MIX_SEQ",
                $sformatf("ISO round PASSED (%0d bytes verified).", ISO_BYTES),
                UVM_LOW)
        else
            `uvm_error("USB_HS_INT_ISO_MIX_SEQ",
                $sformatf("ISO round FAILED: %0d/%0d bytes mismatched.",
                          iso_err_cnt, ISO_BYTES))
    endtask

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;
        int unsigned          total_err_cnt;

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        total_err_cnt = 0;

        // Step 1: wait for the HS host link to reach ENABLED (the VIP has
        // already driven SE0 + chirp, so the DUT has seen its bus reset).
        wait_for_link_enabled(shared_status, "HS host link");

        // Step 2: keep the link alive.
        start_sof_generation();

        // Step 3: post-reset settling delay (firmware DRES_C handling and EP0
        // re-arm).
        #50us;

        // Step 4: enumerate the hub at address 1 and USBDC0 at address 2.
        enumerate_hub_and_usbdc0(host_agent_h, usb_cfg);
        `uvm_info("USB_HS_INT_ISO_MIX_SEQ", "Enumeration complete.", UVM_LOW)
        #10us;

        // Phase 0: INTERRUPT loopback on EP1 (pattern base 0).
        run_int_round(host_agent_h, usb_cfg, INT_EP,
                      INT_OUT_ANCHOR, INT_IN_ANCHOR, 0, total_err_cnt);
        #50us;

        // Phase 1: ISOCHRONOUS round on EP2.
        run_iso_round(host_agent_h, usb_cfg, total_err_cnt);
        #50us;

        // Phase 2: INTERRUPT loopback on EP3 with a shifted pattern.
        run_int_round(host_agent_h, usb_cfg, INT_EP2,
                      INT2_OUT_ANCHOR, INT2_IN_ANCHOR, INT_ROUND_OFFSET,
                      total_err_cnt);

        if (total_err_cnt == 0)
            `uvm_info("USB_HS_INT_ISO_MIX_SEQ",
                "Mixed INT(EP1)/ISO(EP2)/INT(EP3) sequence PASSED - all phases clean.",
                UVM_LOW)
        else
            `uvm_error("USB_HS_INT_ISO_MIX_SEQ",
                $sformatf("Mixed INT/ISO sequence FAILED: %0d total byte mismatches.",
                          total_err_cnt))

        `uvm_info("USB_HS_INT_ISO_MIX_SEQ",
            "USB HS device mixed INTERRUPT + ISOCHRONOUS sequence complete.",
            UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_INT_ISO_MIX_SEQUENCE_SV
