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

`ifndef CALIPTRA_SS_USB_HS_DEV_HUB_BYPASS_ENUM_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_HUB_BYPASS_ENUM_SEQUENCE_SV

// =============================================================================
// High-Speed HUB BYPASS enumeration of USBDC0 (device0 directly on the bus).
//
// WHAT THIS COVERS
//
// The compound IP contains a 2-port hub with two embedded device controllers.
// hub_enable is NOT a strap: USB_EnableHub is tied 1'b0 at top level
// (caliptra_ss_top.sv), so hub_enable_q follows the firmware-written
// HUB_CTRL.HUB_EN bit (ep0_mem(C_HUB_CS)(0), usb_ep0_hub_descr.m.vhdl). With
// HUB_EN left at 0 the compound structure muxes device0 straight onto the
// upstream link - this is the "hub bypass" topology
// (ip_xxx_3511_hs_mem_compound_structure.a.vhdl):
//
//   usb_dev_connect         <= hub_connect when hub_enable_q = '1'
//                              else dev0_usbreg_dev_connect;
//   usbreg_deviceenabled(0) <= hub_connect when hub_enable_q = '1' else '0';
//   usbreg_deviceenabled(1) <= hub_port_enable(0) and dev0_usbreg_deviceenabled
//                              when hub_enable_q = '1'
//                              else dev0_usbreg_deviceenabled;
//   upd_dev0_portreset      <= dev0_portreset when hub_enable_q = '1'
//                              else sync_busreset;
//
// So with HUB_EN = 0 four things change at once: device0 owns the upstream
// connect, the hub is not a bus participant at all, device0's own enable is
// ungated by any hub port enable, and device0's port reset comes straight from
// the upstream bus reset instead of from the hub's per-port reset logic. Every
// other enumerating USB test in this suite runs with HUB_EN = 1, so the
// else-legs of all four of those muxes are only exercised here.
//
// HOST-SIDE CONSEQUENCE AND WHY THE BASE HELPERS ARE NOT USED
//
// In bypass topology there is exactly ONE device on the bus and it is USBDC0.
// The 3-step hub-aware enumeration (hub_enum_stepA / hub_port_bringup_stepB /
// usbdc0_enum_stepC) is therefore wrong here: there is no hub to address at 1,
// no downstream port to power or reset, and USBDC0 answers at the default
// address 0 from the start. This sequence deliberately writes its own flat
// enumeration inline and calls NO hub helper, so the base sequence class needs
// no modification and nothing shared changes behaviour.
//
// The resulting address map differs from every hub-mode test:
//   hub-mode   : hub -> address 1, USBDC0 -> address 2
//   bypass here: USBDC0 -> address 1, hub never addressed
//
// SEQUENCE FLOW
//   1. Resolve handles, start SOF, wait for the host link to reach ENABLED.
//      The link comes up on device0's own DCON (not the hub's), which is the
//      first thing the bypass mux has to get right.
//   2. #SETTLE_DELAY so the firmware can service its bus-reset interrupt
//      (DRES_C) and re-prime EP0 before the first SETUP arrives.
//   3. GET_DESCRIPTOR(DEVICE, 18) at address 0, checked against the dev0
//      device descriptor. A hub descriptor here would mean the hub answered
//      and the bypass did not take effect.
//   4. GET_STATUS(DEVICE) at address 0, expect 0x0001 (bit[0] Self-Powered is
//      hardcoded by the usb.c EP0 handler - see step 3 in the body).
//   5. SET_ADDRESS(1) at address 0, then the mandatory VIP anchor update.
//   6. GET_DESCRIPTOR(DEVICE, 18) at address 1, with the committed-address
//      check read out of RTL on dev0 (not on hub).
//   7. GET_CONFIGURATION at address 1, expect 0 (not yet configured).
//   8. SET_CONFIGURATION(1), then GET_CONFIGURATION verify, expect 1.
//   9. Negotiated-speed check: HS. The bypass path reparents the port-reset
//      source (upd_dev0_portreset), so the chirp handshake runs through a
//      different reset net than in hub mode and the speed must be re-asserted
//      here rather than assumed.
//  10. Settling delay so the firmware can finish its own bookkeeping and
//      report its verdict before the objection drops.
//
// NEGATIVE ASSERTION: the hub must never be addressed
//
// The hub's committed address (usb_dev_addr_probe.hub_dev_addr) must stay 0
// for the whole run. In hub mode it becomes 1 at step A. Checking it here is
// what distinguishes "device0 answered because the bypass works" from
// "something answered". It is checked after enumeration completes.
// =============================================================================

class caliptra_ss_usb_hs_dev_hub_bypass_enum_sequence
    extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_hub_bypass_enum_sequence)

    // Post-link settling delay before the first SETUP. Same 20 us the other HS
    // sequences use; it covers the firmware DRES_C service plus EP0 re-prime.
    localparam time SETTLE_DELAY = 20us;

    // Tail delay before dropping the objection. wait_xfer_done() only proves
    // the bus transaction ended, not that the firmware finished its own
    // post-transfer bookkeeping and printed its verdict.
    localparam time DRAIN_DELAY = 50us;

    // DEVCMDSTAT.Speed encoding from usb_subcmp_pkg.p.vhdl:
    // FULL_SPEED = 2'b01, HIGH_SPEED = 2'b10.
    localparam bit [1:0] SPEED_HS = 2'b10;

    // Address assigned to USBDC0. In bypass topology USBDC0 is the only device
    // on the bus, so it takes address 1 - NOT the address 2 used by every
    // hub-mode test, where address 1 already belongs to the hub.
    localparam bit [6:0] DEV0_ADDRESS = 7'd1;

    function new(string name = "caliptra_ss_usb_hs_dev_hub_bypass_enum_sequence");
        super.new(name);
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;
        bit                   xfer_fail;

        resolve_xfer_handles(host_agent_h, usb_cfg, shared_status);

        `uvm_info("USB_HUB_BYPASS",
            {"Hub-bypass topology: firmware leaves HUB_CTRL.HUB_EN clear, so ",
             "device0 drives the upstream connect directly and the hub is not ",
             "a bus participant. Enumerating USBDC0 at address 1 with no hub ",
             "enumeration and no downstream port bring-up."},
            UVM_NONE)

        // -----------------------------------------------------------------
        // Step 1: SOF on, then wait for the link.
        //
        // The link can only reach ENABLED if dev0_usbreg_dev_connect reached
        // the upstream port through the hub_enable_q = '0' leg of the
        // usb_dev_connect mux, so this wait is already the first functional
        // check of the bypass. wait_for_link_enabled() is bounded and raises a
        // uvm_error on expiry; bail out rather than issue transfers into a
        // dead link.
        // -----------------------------------------------------------------
        start_sof_generation();
        wait_for_link_enabled(shared_status, "HS host link (hub bypass)");
        if (link_wait_timed_out) begin
            `uvm_error("USB_HUB_BYPASS",
                {"Link never reached ENABLED in hub-bypass topology. Most ",
                 "likely the firmware did not assert DEVCMDSTAT.DCON on ",
                 "device0, or it set HUB_CTRL.HUB_EN after all (in which case ",
                 "the hub owns the connect and this test is invalid)."})
            return;
        end

        #SETTLE_DELAY;

        // -----------------------------------------------------------------
        // Step 2: GET_DESCRIPTOR(DEVICE) at the default address 0.
        //
        // The data check is the discriminator for this whole test: in bypass
        // topology device0 answers address 0, so the payload must be the dev0
        // device descriptor. If the hub had answered (HUB_EN = 1) the bytes
        // would be the hub's class-0x09 descriptor and check_device_descriptor
        // against "dev0" would fail.
        // -----------------------------------------------------------------
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h06),       // GET_DESCRIPTOR
            .wvalue               (16'h0100),    // DEVICE descriptor, index 0
            .windex               (16'h0000),
            .wlength              (16'h0012),    // 18 bytes
            .device_addr          (0),
            .label                ("BYPASS_GET_DESC_DEV_addr0"),
            .usb_cfg              (usb_cfg));
        wait_and_check_xfer(.agent_h          (host_agent_h),
                            .label            ("BYPASS_GET_DESC_DEV_addr0"),
                            .min_payload_bytes(18),
                            .fail             (xfer_fail));
        if (xfer_fail) begin
            `uvm_error("USB_HUB_BYPASS",
                {"First control transfer at address 0 failed. In bypass ",
                 "topology USBDC0 itself must answer the default address; ",
                 "abandoning the rest of the enumeration."})
            return;
        end
        usb_data_check_api.check_device_descriptor(.usb_item(last_ctrl_seq_item),
                                                   .device_name("dev0"));

        // -----------------------------------------------------------------
        // Step 3: GET_STATUS(DEVICE) at address 0.
        //
        // Expect 0x0001, NOT 0x0000. Do not derive this value from the USB
        // spec - read the handler. The shared library hardcodes bit[0]
        // Self-Powered to 1 for the embedded device controllers
        // (usb.c, USB_REQ_GET_STATUS in the Standard/Device branch):
        //
        //   uint32_t status_buf = 0x00000001u
        //                       | (usb_remote_wakeup_enabled ? 0x2u : 0x0u);
        //
        // bit[1] Remote-Wakeup is 0 because nothing in this test issues
        // SET_FEATURE(DEVICE_REMOTE_WAKEUP). So the only two values this
        // firmware can ever return for recipient=device are 0x0001 and, after
        // a SET_FEATURE, 0x0003 - which is exactly what the pre-existing
        // caliptra_ss_usb_hs_dev_get_status test asserts. An earlier revision
        // of this sequence expected 0x0000 and failed here with
        // "expected 0x0000 got 0x0001"; the device was right and the sequence
        // was wrong.
        // -----------------------------------------------------------------
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h00),       // GET_STATUS
            .wvalue               (16'h0000),
            .windex               (16'h0000),
            .wlength              (16'h0002),    // 2 bytes
            .device_addr          (0),
            .label                ("BYPASS_GET_STATUS_addr0"),
            .usb_cfg              (usb_cfg));
        wait_and_check_xfer(.agent_h          (host_agent_h),
                            .label            ("BYPASS_GET_STATUS_addr0"),
                            .min_payload_bytes(2),
                            .fail             (xfer_fail));
        if (!xfer_fail)
            usb_data_check_api.check_get_status(.usb_item(last_ctrl_seq_item),
                                                .device_name("dev0"),
                                                .expected(16'h0001));

        // -----------------------------------------------------------------
        // Step 4: SET_ADDRESS(1) at address 0, then re-anchor the VIP.
        //
        // The anchor update is mandatory and must be in lockstep with the
        // request: the VIP fixed_dev_ep_ustr_valid_ranges constraint otherwise
        // contradicts the inline device_address constraint of the next
        // randomize() and the solver issues a UVM_FATAL. The #5us in between
        // is the USB 2.0 section 9.4.6 SetAddress() recovery interval, which
        // the firmware needs to commit the address to DEVCMDSTAT.
        // -----------------------------------------------------------------
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h05),       // SET_ADDRESS
            .wvalue               (16'(DEV0_ADDRESS)),
            .windex               (16'h0000),
            .wlength              (16'h0000),
            .device_addr          (0),
            .label                ("BYPASS_SET_ADDRESS_1"),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(host_agent_h, "BYPASS_SET_ADDRESS_1");
        #5us;

        usb_cfg.remote_device_cfg[0].device_address = DEV0_ADDRESS;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_HUB_BYPASS",
            $sformatf("VIP anchor moved to device_address=%0d (USBDC0).",
                      DEV0_ADDRESS),
            UVM_NONE)

        // -----------------------------------------------------------------
        // Step 5: GET_DESCRIPTOR(DEVICE) at the new address.
        //
        // Proves USBDC0 accepted SET_ADDRESS and now answers on address 1.
        // The address check reads the committed address straight out of RTL
        // (usb_reg_if_1.usbreg_usbaddress via usb_dev_addr_probe), so it is
        // independent of the payload. Gated on the transfer actually having
        // moved data, otherwise a wholly failed enumeration can score a pass.
        // -----------------------------------------------------------------
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h06),
            .wvalue               (16'h0100),
            .windex               (16'h0000),
            .wlength              (16'h0012),
            .device_addr          (int'(DEV0_ADDRESS)),
            .label                ("BYPASS_GET_DESC_DEV_addr1"),
            .usb_cfg              (usb_cfg));
        wait_and_check_xfer(.agent_h          (host_agent_h),
                            .label            ("BYPASS_GET_DESC_DEV_addr1"),
                            .min_payload_bytes(18),
                            .fail             (xfer_fail));
        if (!xfer_fail) begin
            usb_data_check_api.check_device_descriptor(.usb_item(last_ctrl_seq_item),
                                                       .device_name("dev0"));
            usb_data_check_api.check_device_address(.usb_item(last_ctrl_seq_item),
                                                    .device_name("dev0"),
                                                    .expected_address(int'(DEV0_ADDRESS)));
        end

        // -----------------------------------------------------------------
        // Step 6: GET_CONFIGURATION before SET_CONFIGURATION.
        //
        // Returns the 1-byte bConfigurationValue, which must still be 0: the
        // device is in the Address state, not the Configured state
        // (USB 2.0 section 9.4.2).
        // -----------------------------------------------------------------
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h08),       // GET_CONFIGURATION
            .wvalue               (16'h0000),
            .windex               (16'h0000),
            .wlength              (16'h0001),
            .device_addr          (int'(DEV0_ADDRESS)),
            .label                ("BYPASS_GET_CONFIG_addr1"),
            .usb_cfg              (usb_cfg));
        wait_and_check_xfer(.agent_h          (host_agent_h),
                            .label            ("BYPASS_GET_CONFIG_addr1"),
                            .min_payload_bytes(1),
                            .fail             (xfer_fail));

        // -----------------------------------------------------------------
        // Step 7: SET_CONFIGURATION(1), then read it back.
        //
        // These two are issued back to back with no delay, which is exactly
        // the case that makes the shared-notification race in wait_xfer_done()
        // observable, so both use the forked do_control_xfer_and_wait() form.
        // Reaching the Configured state (USB 2.0 section 9.1.1.5) is what
        // makes this a complete enumeration rather than a partial one.
        // -----------------------------------------------------------------
        do_control_xfer_and_wait(
            .agent_h              (host_agent_h),
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h09),       // SET_CONFIGURATION
            .wvalue               (16'h0001),
            .windex               (16'h0000),
            .wlength              (16'h0000),
            .device_addr          (int'(DEV0_ADDRESS)),
            .label                ("BYPASS_SET_CONFIG_1"),
            .usb_cfg              (usb_cfg),
            .fail                 (xfer_fail));

        do_control_xfer_and_wait(
            .agent_h              (host_agent_h),
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h08),       // GET_CONFIGURATION
            .wvalue               (16'h0000),
            .windex               (16'h0000),
            .wlength              (16'h0001),
            .device_addr          (int'(DEV0_ADDRESS)),
            .label                ("BYPASS_GET_CONFIG_verify"),
            .usb_cfg              (usb_cfg),
            .min_payload_bytes    (1),
            .fail                 (xfer_fail));

        if(xfer_fail)
            `uvm_error("USB_HUB_BYPASS", "BYPASS_GET_CONFIG_verify failed")

        // -----------------------------------------------------------------
        // Step 8: negotiated speed must be High Speed.
        //
        // Checked explicitly because the bypass mux reparents the port-reset
        // source: upd_dev0_portreset takes sync_busreset directly instead of
        // the hub's dev0_portreset. The chirp handshake therefore runs through
        // a different reset net than in every other test, and a missed chirp
        // would silently leave the link at Full Speed with enumeration still
        // succeeding. Read from RTL through usb_dev_addr_probe, so no transfer
        // is involved.
        // -----------------------------------------------------------------
        usb_data_check_api.check_device_speed("dev0", SPEED_HS);

        // -----------------------------------------------------------------
        // Step 9: negative assertion - the hub was never addressed.
        //
        // hub_dev_addr is the hub's committed device address. In hub mode step
        // A drives it to 1. In bypass topology the hub is not on the bus at
        // all and must still read 0. This is what makes the positive result
        // above specific to the bypass path rather than merely "some device
        // enumerated".
        //
        // check_device_address() reads the committed address out of RTL and
        // uses its usb_item only as a validity gate ("did the enumeration this
        // address is attributed to actually happen"), not as the data source,
        // so the last successful transfer of the enumeration is the correct
        // item to pass. It must NOT be null - the implementation casts the
        // argument unconditionally and issues a uvm_fatal on a null handle.
        // No transfer is addressed to the hub anywhere in this test, and none
        // should be: addressing the hub on purpose would perturb the topology
        // under test.
        // -----------------------------------------------------------------
        if (!xfer_fail)
            usb_data_check_api.check_device_address(.usb_item(last_ctrl_seq_item),
                                                    .device_name("hub"),
                                                    .expected_address(0));
        else
            `uvm_error("USB_HUB_BYPASS",
                {"Skipping the hub-never-addressed check: the final ",
                 "enumeration transfer did not complete, so there is no valid ",
                 "transfer to attribute the RTL address state to."})

        // Let the firmware finish its bookkeeping and print its verdict
        // before the objection drops and the environment calls $finish.
        #DRAIN_DELAY;

        `uvm_info("USB_HUB_BYPASS",
            {"Hub-bypass enumeration of USBDC0 complete: device0 answered the ",
             "default address, took address 1, reached the Configured state at ",
             "High Speed, and the hub was never addressed."},
            UVM_NONE)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_HUB_BYPASS_ENUM_SEQUENCE_SV
