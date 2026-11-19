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

`ifndef CALIPTRA_SS_USB_HS_HUB_EP0_UNSUPPORTED_FEATURES_VALID_PORT_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_HUB_EP0_UNSUPPORTED_FEATURES_VALID_PORT_SEQUENCE_SV

// =============================================================================
// Hub EP0 control requests for UNSUPPORTED features, plus SETUP mask/length
// patterns that differ from the standard request set, GetConfiguration and the
// EP0 IN STALL paths.
//
// This is a CODE COVERAGE directed test for usb_ep0_handler.m.vhdl. It is a
// host-misbehaviour scenario: every request below is legal on the wire but is
// either unsupported by the hub or carries a field combination the hub
// SETUP-match table does not admit, so the required behaviour is an EP0 STALL
// (or a clamped data stage), not a normal completion.
//
// Hub-only enumeration (hub_enum_stepA, hub at address 1). All nine steps are
// EP0 control transfers; no data endpoint is ever touched, so none of the
// data-transfer hazards of the endpoint-halt / unsupported-endpoint tests
// apply here.
//
// -----------------------------------------------------------------------------
// 1. How the hub SETUP-match table works (MEASURED, usb_ep0_handler.m.vhdl
//    PROC_SETUP_DECODE, and usb_ep0_hub_descr.m.vhdl func_ep0_rom)
// -----------------------------------------------------------------------------
// Each supported request is FOUR 32-bit words in the hub table, walked by the
// PROC_SETUP_DECODE state machine:
//
//   word A   (READ_SETUP_LSB)      low  16 = match on {bmRequestType,bRequest}
//                                  high 16 = expected wValue -> setup_check
//   word A+1 (READ_SETUP_MASK_LSB) high 16 = wValue MASK
//                                  bits 6:0 = setup_request opcode
//                                  bit  7   = LAST (end of this device table)
//                                  bits 15:8 = data buffer selector
//   word A+2 (READ_SETUP_MSB)      low  16 = expected wIndex -> setup_check
//                                  high 16 = ROM wLength CAP
//   word A+3 (READ_SETUP_MASK_MSB) low  16 = wIndex MASK
//
// Mask polarity is MEASURED from line 228
// (var_setup_masked := rdata and setup_bytes): a mask bit of 1 means the bit
// is COMPARED, 0 means don't-care.
//
// The three outcomes of a row, and the RTL lines this test targets:
//
//   a) LSB+wValue match and wIndex match        -> SETUP_DONE, request accepted
//      (lines 231-237, already covered by every existing USB test)
//   b) LSB or wValue mismatch on a NON-last row -> READ_SETUP_LSB, next row
//      (lines 209-211, already covered)
//   c) LSB or wValue mismatch on the LAST row   -> SETUP_DONE with
//      setup_request cleared and NEITHER ep0_in_active nor ep0_out_active set,
//      which is how this IP produces an EP0 STALL
//      (lines 205-207, FSM arc READ_SETUP_MASK_LSB -> SETUP_DONE)
//   d) LSB+wValue match but wIndex mismatch on a NON-last row -> READ_SETUP_LSB
//      (lines 244-246, FSM arc READ_SETUP_MASK_MSB -> READ_SETUP_LSB)
//   e) LSB+wValue match but wIndex mismatch on the LAST row -> STALL
//      (lines 239-241, FSM arc READ_SETUP_MASK_MSB -> SETUP_DONE; see step 8)
//
// -----------------------------------------------------------------------------
// 2. Step list and the RTL line each step targets
// -----------------------------------------------------------------------------
//  1 GET_CONFIGURATION wLength=1          COMPLETE, data 0x01   lines 360-361
//  2 GET_CONFIGURATION wLength=2          COMPLETE, 1 byte      line  219 (clamp)
//  3 GET_STATUS(INTERFACE) wLength=2      COMPLETE, 0x0000      line  372
//  4 GET_STATUS(DEVICE) wLength=4         COMPLETE, 2 bytes     line  219 again
//  5 SET_FEATURE(DEVICE) wValue=0x0003    STALL                 line  341
//  6 GET_STATUS(ENDPOINT) wIndex=0x0082   STALL                 lines 244-246
//                                                               then 205-207
//  7 SYNCH_FRAME (bRequest 0x0C)          STALL                 lines 205-207
//  8 SET_AND_TEST_HUB_PORT_FEATURE        STALL                 lines 239-241
//  9 GET_CONFIGURATION wLength=1          COMPLETE              recovery proof
//
// Step 2 and step 4 target the wLength clamp at line 218-220
//   if ep0_mem_rdata_int(31 downto 16) < setup_bytes(device)(63 downto 48)
// i.e. the ROM cap is SMALLER than the wLength the host asked for. Every
// pre-existing USB test asks for exactly the ROM cap (GET_DESCRIPTOR 0x12
// against a cap of 0x0012, and so on), so the clamp was never taken. The
// GetConfiguration row caps at 0x0001 and the GetStatus(Device) row at
// 0x0002, so wLength 2 and 4 respectively take it.
//
// Step 5 is an UNSUPPORTED FEATURE on a valid recipient. The
// SetFeature(Device) row has wValue mask 0xFFFC against expected wValue
// 0x0000, so wValue bits 1:0 are don't-care and wValue = 0x0003 is ADMITTED by
// the table. PROC_STD_REQ_DECODE then rejects it at line 339-341:
//   if setup_bytes(device)(17 downto 16) = "11" then ep0_in_stall <= '1';
// (feature selector 3 is not a defined device feature: bit 0 is
// DEVICE_REMOTE_WAKEUP, bit 1 is TEST_MODE, and asking for both at once is
// illegal). Note the side effect at line 334-337: wValue bit 0 is set, so
// set_remote_wake_enabled also pulses and ep0_remote_wake_enabled_int(0)
// becomes 1 even though the request is stalled. That is why step 4
// (GET_STATUS(DEVICE), whose bit 1 is that flop) runs BEFORE step 5.
//
// Step 6 is a SETUP mask pattern that differs from the standard set: the
// GetStatus(Endpoint) row has wIndex mask 0xFF7E, so bits 1..6 and 8..15 are
// compared against 0x0000 while bits 0 and 7 are don't-care. wIndex = 0x0082
// (endpoint 2, direction IN) therefore matches the request opcode but
// MISMATCHES the masked wIndex, which is outcome (d). The walk resumes and
// eventually falls off the end of the table, so this single request covers
// BOTH targeted FSM arcs.
//
// Step 8 needs the firmware table patch - see section 3.
//
// -----------------------------------------------------------------------------
// 3. Why step 8 needs a firmware table patch (MEASURED)
// -----------------------------------------------------------------------------
// Outcome (e) above (lines 239-241) requires the LAST row of the device table
// to match on {bmRequestType,bRequest} and wValue but MISMATCH on the masked
// wIndex. With the reset table that is arithmetically impossible: the last row
// of device 0 is SetAndTestHubPortFeature (usb_ep0_hub_descr.m.vhdl:421-425)
// and its SETUP_MASK_MSB is X"00000000", i.e. wIndex is ENTIRELY don't-care,
// so a matched row can never mismatch on wIndex.
//
// The hub table is NOT a ROM at run time. C_EP0_ROM is only the reset value of
// the writable array ep0_mem (usb_ep0_hub_descr.m.vhdl:72, :476) and any of
// the C_NWORDS = 196 words is writable from the hub register port while
// hub_write_lock is 0 (:495-502). hub_write_lock is
// HUB_CS(0) and HUB_CS(16) (:528), i.e. HUB_EN and HUB_DCON, so the window is
// before usb_hub_init_and_connect().
//
// The firmware of this test (caliptra_ss_usb_hs_hub_ep0_unsupported_features_valid_port.c)
// therefore writes word 195 - the SETUP_MASK_MSB of that last row, absolute
// address 0x2000_130C - from 0x00000000 to 0x0000FFFF before
// boot_usb_core_hub(). wIndex then becomes fully compared against the expected
// 0x0000 of word 194, and the request below with wIndex = 0x0001 takes
// lines 239-241.
//
// Containment: SetAndTestHubPortFeature (bmRequestType 0xA3, bRequest 0x0C) is
// issued by NO other test in the tree, and the patch is a run-time register
// write done only by this test's own firmware, so no other test is affected.
//
// Field constraints of that row, read from the four words
//   192 X"00000CA3"  193 X"FFE040C3"  194 X"00010000"  195 X"00000000":
//   bmRequestType = 0xA3 (DEVICE_TO_HOST | CLASS | recipient OTHER)
//   bRequest      = 0x0C
//   wValue mask   = 0xFFE0 against expected 0x0000 -> wValue must be <= 0x001F
//   expected wIndex = 0x0000, ROM wLength cap = 0x0001
// so wValue = 0x0000 / wIndex = 0x0001 / wLength = 2 satisfies the match on
// everything except wIndex, which is exactly outcome (e).
//
// -----------------------------------------------------------------------------
// 4. Documented coverage waivers (no stimulus exists - do NOT try to write one)
// -----------------------------------------------------------------------------
// line 165  device <= device + 1 (IDLE round-robin) is STRUCTURALLY DEAD in
//           this configuration: usb_ep_config_hub_pkg.p.vhdl:26 sets
//           C_NBDEV = 1, so the guard at line 162 (device = C_NBDEV-1) is a
//           tautology and the else leg can never execute.
// line 477  PROC_EP0_MEM_ACCESS SETUP_DECODE -> USB_DATA on a grant with a
//           pending upd_dma_req. This is an internal arbiter race between the
//           SETUP walk and the EP0 data path and cannot be driven directly.
//           The long table walks of steps 6, 7 and 8 are the longest possible
//           SETUP_DECODE occupancies in this IP and so maximise the chance of
//           hitting it, but it is not asserted by this test.
//
// Full write-up: docs/usb/usb_ep0_handler_coverage_map.md (accessories repo).
// =============================================================================

class caliptra_ss_usb_hs_hub_ep0_unsupported_features_valid_port_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_hub_ep0_unsupported_features_valid_port_sequence)

    // USB device address assigned to the hub by hub_enum_stepA.
    localparam int HUB_ADDR = 1;

    // Standard / class request codes used below.
    localparam bit [7:0] BREQ_GET_STATUS        = 8'h00;
    localparam bit [7:0] BREQ_SET_FEATURE       = 8'h03;
    localparam bit [7:0] BREQ_GET_CONFIGURATION = 8'h08;
    // 0x0C is SYNCH_FRAME in the standard request set and, with
    // bmRequestType 0xA3, SetAndTestHubPortFeature in the hub class.
    localparam bit [7:0] BREQ_SYNCH_FRAME       = 8'h0C;
    localparam bit [7:0] BREQ_SET_AND_TEST      = 8'h0C;

    // Feature selector 3 = DEVICE_REMOTE_WAKEUP and TEST_MODE at the same
    // time. Admitted by the SETUP-match table, rejected by the handler.
    localparam bit [15:0] FEATURE_UNSUPPORTED_DEV = 16'h0003;

    // wIndex of the step 6 probe: endpoint 2, direction IN. Masked with the
    // row's 0xFF7E this leaves bit 1 set, so the row mismatches.
    localparam bit [15:0] EP_WINDEX_MISMATCH = 16'h0082;

    // wIndex of the step 8 probe: hub downstream port 1. Non-zero, so with the
    // patched mask it mismatches the row's expected 0x0000.
    localparam bit [15:0] PORT_WINDEX_MISMATCH = 16'h0001;

    // Only one configuration exists, and hub_enum_stepA has already selected
    // it, so GET_CONFIGURATION must return 0x01.
    localparam bit [7:0] EXPECTED_CONFIG_VALUE = 8'h01;

    // Expected bus-level outcome passed to check_setup_stalled(). A control
    // transfer the device terminates with a STALL handshake is reported by the
    // VIP as svt_sequence_item::ABORTED.
    localparam bit XFER_MUST_STALL    = 1'b1;
    localparam bit XFER_MUST_COMPLETE = 1'b0;

    function new(string name = "caliptra_ss_usb_hs_hub_ep0_unsupported_features_valid_port_sequence");
        super.new(name);
    endfunction

    // -------------------------------------------------------------------------
    // Bus-level accept/reject check for the control transfer just issued.
    //
    // Must be called after wait_xfer_done(), which blocks on
    // NOTIFY_USB_TRANSFER_ENDED, so the status field of the cached item is
    // final by the time it is read. last_ctrl_seq_item is populated by
    // do_control_xfer(); the null guard is a uvm_fatal so a refactor that
    // drops that cast cannot silently disable this check.
    //
    // Same mechanism as caliptra_ss_usb_hs_hub_test_mode_sequence.
    // -------------------------------------------------------------------------
    function void check_setup_stalled(bit    expect_stalled,
                                      string label,
                                      string rtl_reference);
        bit observed_stall;

        if (last_ctrl_seq_item == null)
            `uvm_fatal("USB_HUB_EP0_UNSUP_FEAT",
                $sformatf({"%s: last_ctrl_seq_item is null, the transfer ",
                           "status cannot be checked."}, label))

        observed_stall = (last_ctrl_seq_item.status == svt_sequence_item::ABORTED);

        if (expect_stalled && !observed_stall) begin
            `uvm_error("USB_HUB_EP0_UNSUP_FEAT",
                $sformatf({"%s: the hub did NOT stall an unsupported request. ",
                           "Transfer status is %p, expected ABORTED. ",
                           "Expected RTL behaviour: %s."},
                          label, last_ctrl_seq_item.status, rtl_reference))
        end
        else if (!expect_stalled && observed_stall) begin
            `uvm_error("USB_HUB_EP0_UNSUP_FEAT",
                $sformatf({"%s: the hub STALLed a request it must accept. ",
                           "Transfer status is ABORTED. ",
                           "Expected RTL behaviour: %s."},
                          label, rtl_reference))
        end
        else begin
            `uvm_info("USB_HUB_EP0_UNSUP_FEAT",
                $sformatf({"%s: bus-level outcome as expected (stalled=%0b, ",
                           "status=%p) at %0t. RTL: %s."},
                          label, observed_stall, last_ctrl_seq_item.status,
                          $time, rtl_reference),
                UVM_LOW)
        end
    endfunction

    // -------------------------------------------------------------------------
    // Payload byte-count check for a completed control read. Used for the
    // wLength clamp steps, where the device must return FEWER bytes than the
    // host asked for because the ROM cap is smaller.
    // -------------------------------------------------------------------------
    function void check_payload_bytes(int unsigned expected_bytes,
                                      string       label);
        int unsigned observed_bytes;

        if (last_ctrl_seq_item == null)
            `uvm_fatal("USB_HUB_EP0_UNSUP_FEAT",
                $sformatf({"%s: last_ctrl_seq_item is null, the payload size ",
                           "cannot be checked."}, label))

        observed_bytes = last_ctrl_seq_item.payload_byte_count();

        if (observed_bytes != expected_bytes) begin
            `uvm_error("USB_HUB_EP0_UNSUP_FEAT",
                $sformatf({"%s: data stage returned %0d bytes, expected %0d. ",
                           "The hub must clamp the data stage to the ROM ",
                           "wLength cap (usb_ep0_handler.m.vhdl:218-220)."},
                          label, observed_bytes, expected_bytes))
        end
        else begin
            `uvm_info("USB_HUB_EP0_UNSUP_FEAT",
                $sformatf("%s: data stage returned the expected %0d bytes.",
                          label, observed_bytes),
                UVM_LOW)
        end
    endfunction

    // -------------------------------------------------------------------------
    // Single-byte data check for GET_CONFIGURATION. The handler drives
    // setup_data(7 downto 1) to zero and setup_data(0) to the stored
    // configuration bit (usb_ep0_handler.m.vhdl:359-361), so the whole byte
    // must equal the configuration value.
    // -------------------------------------------------------------------------
    function void check_configuration_value(bit [7:0] expected,
                                            string    label);
        bit [7:0] observed;

        if (last_ctrl_seq_item == null)
            `uvm_fatal("USB_HUB_EP0_UNSUP_FEAT",
                $sformatf({"%s: last_ctrl_seq_item is null, the configuration ",
                           "value cannot be checked."}, label))

        if (last_ctrl_seq_item.payload_byte_count() < 1) begin
            `uvm_error("USB_HUB_EP0_UNSUP_FEAT",
                $sformatf({"%s: GET_CONFIGURATION returned no data byte ",
                           "(payload_byte_count = %0d)."},
                          label, last_ctrl_seq_item.payload_byte_count()))
            return;
        end

        observed = last_ctrl_seq_item.payload.data[0];

        if (observed != expected) begin
            `uvm_error("USB_HUB_EP0_UNSUP_FEAT",
                $sformatf({"%s: GET_CONFIGURATION returned 0x%02h, expected ",
                           "0x%02h. Only one configuration exists and ",
                           "hub_enum_stepA already selected it."},
                          label, observed, expected))
        end
        else begin
            `uvm_info("USB_HUB_EP0_UNSUP_FEAT",
                $sformatf("%s: GET_CONFIGURATION returned the expected 0x%02h.",
                          label, observed),
                UVM_LOW)
        end
    endfunction

    // -------------------------------------------------------------------------
    // GET_CONFIGURATION (bmRequestType 0x80, bRequest 0x08). wlength is a
    // parameter so the same helper serves the nominal read and the clamp probe.
    // -------------------------------------------------------------------------
    task get_configuration(svt_usb_agent         host_agent_h,
                           svt_usb_configuration usb_cfg,
                           bit [15:0]            wlength,
                           string                label);
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (BREQ_GET_CONFIGURATION),
            .wvalue               (16'h0000),
            .windex               (16'h0000),
            .wlength              (wlength),
            .device_addr          (HUB_ADDR),
            .label                (label),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label(label));
    endtask

    // -------------------------------------------------------------------------
    // Main body
    // -------------------------------------------------------------------------
    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;
        bit [15:0]            expected_dev_status;

        `uvm_info("USB_HUB_EP0_UNSUP_FEAT",
            "Auto-attach in flight via remote_cfg. Waiting for host link to reach ENABLED.",
            UVM_LOW)

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 0a: Wait for the host link to reach ENABLED (bounded wait).
        wait_for_link_enabled(shared_status, "host link");
        if (link_wait_timed_out) begin
            `uvm_error("USB_HUB_EP0_UNSUP_FEAT",
                "Link never reached ENABLED; aborting hub EP0 unsupported-request sequence.")
            return;
        end

        // Step 0b: Start SOF generation so the link stays out of SUSPENDED,
        // then let the bus settle before the first SETUP transfer.
        start_sof_generation();
        #20us;

        // Step 0c: Enumerate the hub alone at address 1. The downstream ports
        // are deliberately left un-powered: every request below is addressed
        // to the hub itself. This also performs SET_CONFIGURATION(1), which is
        // what makes the GET_CONFIGURATION checks below expect 0x01.
        hub_enum_stepA(host_agent_h, usb_cfg);

        // ---------------------------------------------------------------------
        // Step 1: GET_CONFIGURATION with the exact ROM wLength cap of 1.
        // Targets usb_ep0_handler.m.vhdl:359-361 (C_STD_REQ_GET_CONFIGURATION
        // data mux). No existing test issues this request to the HUB.
        // ---------------------------------------------------------------------
        get_configuration(host_agent_h, usb_cfg, 16'h0001,
                          "GET_CONFIGURATION_len1_hub");
        check_setup_stalled(XFER_MUST_COMPLETE, "GET_CONFIGURATION_len1_hub",
                            "GetConfiguration is a supported hub request");
        check_configuration_value(EXPECTED_CONFIG_VALUE,
                                  "GET_CONFIGURATION_len1_hub");

        // ---------------------------------------------------------------------
        // Step 2: GET_CONFIGURATION with wLength = 2, which is LARGER than the
        // row's ROM cap of 0x0001. Targets the clamp at
        // usb_ep0_handler.m.vhdl:218-220: the handler overwrites the host
        // wLength with the smaller ROM value, so the data stage must still be
        // a single byte.
        // ---------------------------------------------------------------------
        get_configuration(host_agent_h, usb_cfg, 16'h0002,
                          "GET_CONFIGURATION_len2_clamp_hub");
        check_setup_stalled(XFER_MUST_COMPLETE,
                            "GET_CONFIGURATION_len2_clamp_hub",
                            "an over-long wLength is clamped, not stalled");
        check_payload_bytes(1, "GET_CONFIGURATION_len2_clamp_hub");
        check_configuration_value(EXPECTED_CONFIG_VALUE,
                                  "GET_CONFIGURATION_len2_clamp_hub");

        // ---------------------------------------------------------------------
        // Step 3: GET_STATUS(INTERFACE). Targets
        // usb_ep0_handler.m.vhdl:371-372 (C_STD_REQ_GET_STATUS_IF), which
        // returns an all-zero 16-bit status word as USB 2.0 section 9.4.5
        // requires. wIndex must be 0x0000: the row's wIndex mask is 0xFFFF.
        // ---------------------------------------------------------------------
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_INTERFACE),
            .brequest_val         (BREQ_GET_STATUS),
            .wvalue               (16'h0000),
            .windex               (16'h0000),
            .wlength              (16'h0002),
            .device_addr          (HUB_ADDR),
            .label                ("GET_STATUS_IF_hub"),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label("GET_STATUS_IF_hub"));
        check_setup_stalled(XFER_MUST_COMPLETE, "GET_STATUS_IF_hub",
                            "GetStatus(Interface) is a supported hub request");
        usb_data_check_api.check_get_status(.usb_item(last_ctrl_seq_item),
                                            .device_name("hub"),
                                            .expected(16'h0000));

        // ---------------------------------------------------------------------
        // Step 4: GET_STATUS(DEVICE) with wLength = 4 against a ROM cap of
        // 0x0002 - the second wLength clamp probe (line 218-220).
        //
        // The expected status word is built from the RTL, not from the USB
        // spec (usb_ep0_handler.m.vhdl:366-369): bits 15:2 are zero, bit 1 is
        // ep0_remote_wake_enabled_int and bit 0 is usb_self_powered.
        // Remote wakeup has not been enabled yet - which is precisely why this
        // step runs BEFORE step 5, whose stalled request still latches that
        // flop (line 334-337). Self-powered is taken from the hub
        // CONFIGURATION descriptor bmAttributes D6 that hub_enum_stepA already
        // captured into hub_self_powered, so the expectation tracks the DUT
        // pin rather than a hardcoded guess.
        // ---------------------------------------------------------------------
        expected_dev_status = {15'h0000, hub_self_powered};
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (BREQ_GET_STATUS),
            .wvalue               (16'h0000),
            .windex               (16'h0000),
            .wlength              (16'h0004),
            .device_addr          (HUB_ADDR),
            .label                ("GET_STATUS_DEV_len4_clamp_hub"),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h),
                       .label("GET_STATUS_DEV_len4_clamp_hub"));
        check_setup_stalled(XFER_MUST_COMPLETE,
                            "GET_STATUS_DEV_len4_clamp_hub",
                            "an over-long wLength is clamped, not stalled");
        check_payload_bytes(2, "GET_STATUS_DEV_len4_clamp_hub");
        usb_data_check_api.check_get_status(.usb_item(last_ctrl_seq_item),
                                            .device_name("hub"),
                                            .expected(expected_dev_status));

        // ---------------------------------------------------------------------
        // Step 5: SET_FEATURE(DEVICE) with the UNSUPPORTED feature selector 3.
        // The table admits it (wValue mask 0xFFFC), the handler stalls it at
        // usb_ep0_handler.m.vhdl:339-341.
        // ---------------------------------------------------------------------
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (BREQ_SET_FEATURE),
            .wvalue               (FEATURE_UNSUPPORTED_DEV),
            .windex               (16'h0000),
            .wlength              (16'h0000),
            .device_addr          (HUB_ADDR),
            .label                ("SET_FEATURE_DEV_sel3_hub"),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h),
                       .label("SET_FEATURE_DEV_sel3_hub"));
        check_setup_stalled(XFER_MUST_STALL, "SET_FEATURE_DEV_sel3_hub",
                            {"usb_ep0_handler.m.vhdl:339-341 asserts ",
                             "ep0_in_stall for wValue(1:0) = 11"});

        // ---------------------------------------------------------------------
        // Step 6: GET_STATUS(ENDPOINT) with wIndex = 0x0082. The opcode and
        // wValue match the GetStatus(Endpoint) row but the masked wIndex does
        // not (mask 0xFF7E leaves bit 1 compared), so the walk continues:
        // usb_ep0_handler.m.vhdl:244-246, FSM arc
        // READ_SETUP_MASK_MSB -> READ_SETUP_LSB. The request then matches no
        // further row and falls off the end of the table, taking
        // lines 205-207 (arc READ_SETUP_MASK_LSB -> SETUP_DONE) and stalling.
        // ---------------------------------------------------------------------
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_ENDPOINT),
            .brequest_val         (BREQ_GET_STATUS),
            .wvalue               (16'h0000),
            .windex               (EP_WINDEX_MISMATCH),
            .wlength              (16'h0002),
            .device_addr          (HUB_ADDR),
            .label                ("GET_STATUS_EP_windex_mismatch_hub"),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h),
                       .label("GET_STATUS_EP_windex_mismatch_hub"));
        check_setup_stalled(XFER_MUST_STALL,
                            "GET_STATUS_EP_windex_mismatch_hub",
                            {"usb_ep0_handler.m.vhdl:244-246 continues the ",
                             "walk, then 205-207 stalls at the last row"});

        // ---------------------------------------------------------------------
        // Step 7: SYNCH_FRAME, a standard request this IP does not implement
        // at all, so no row matches on {bmRequestType,bRequest}. This is the
        // longest possible table walk and ends at lines 205-207.
        // ---------------------------------------------------------------------
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_ENDPOINT),
            .brequest_val         (BREQ_SYNCH_FRAME),
            .wvalue               (16'h0000),
            .windex               (16'h0081),
            .wlength              (16'h0002),
            .device_addr          (HUB_ADDR),
            .label                ("SYNCH_FRAME_unsupported_hub"),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h),
                       .label("SYNCH_FRAME_unsupported_hub"));
        check_setup_stalled(XFER_MUST_STALL, "SYNCH_FRAME_unsupported_hub",
                            {"no table row matches, so ",
                             "usb_ep0_handler.m.vhdl:205-207 clears ",
                             "setup_request and EP0 stalls"});

        // ---------------------------------------------------------------------
        // Step 8: SetAndTestHubPortFeature (bmRequestType 0xA3,
        // bRequest 0x0C) with wIndex = 0x0001. This is the LAST row of the hub
        // table, so with the firmware patch of section 3 in place the row
        // matches on opcode and wValue and MISMATCHES on the now-compared
        // wIndex, taking usb_ep0_handler.m.vhdl:239-241 and FSM arc
        // READ_SETUP_MASK_MSB -> SETUP_DONE.
        //
        // If this step does NOT stall, the firmware patch did not take effect
        // (hub_write_lock was already set, or the address is wrong) - check
        // the "hub SETUP table patch" read-back line in mcu_console.log before
        // suspecting the DUT.
        // ---------------------------------------------------------------------
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::CLASS),
            .bm_request_type_recip(svt_usb_types::BMREQ_OTHER),
            .brequest_val         (BREQ_SET_AND_TEST),
            .wvalue               (16'h0000),
            .windex               (PORT_WINDEX_MISMATCH),
            .wlength              (16'h0002),
            .device_addr          (HUB_ADDR),
            .label                ("SET_AND_TEST_PORT_windex_mismatch_hub"),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h),
                       .label("SET_AND_TEST_PORT_windex_mismatch_hub"));
        check_setup_stalled(XFER_MUST_STALL,
                            "SET_AND_TEST_PORT_windex_mismatch_hub",
                            {"usb_ep0_handler.m.vhdl:239-241 stalls a last-row ",
                             "wIndex mismatch (needs the firmware word-195 ",
                             "SETUP_MASK_MSB patch)"});

        // ---------------------------------------------------------------------
        // Step 9: Recovery proof. None of the four stalls above may have
        // wedged the control pipe, so a plain GET_CONFIGURATION must still be
        // answered. Without this step a DUT that dies after the first stall
        // would still pass every check.
        // ---------------------------------------------------------------------
        get_configuration(host_agent_h, usb_cfg, 16'h0001,
                          "GET_CONFIGURATION_recovery_hub");
        check_setup_stalled(XFER_MUST_COMPLETE,
                            "GET_CONFIGURATION_recovery_hub",
                            "EP0 must still answer after the stalled requests");
        check_configuration_value(EXPECTED_CONFIG_VALUE,
                                  "GET_CONFIGURATION_recovery_hub");

        `uvm_info("USB_HUB_EP0_UNSUP_FEAT",
            "USB hub EP0 unsupported-request sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_HUB_EP0_UNSUPPORTED_FEATURES_VALID_PORT_SEQUENCE_SV
