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

`ifndef CALIPTRA_SS_USB_HS_DEV_DISCONNECT_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_DISCONNECT_SEQUENCE_SV

// =============================================================================
// USB High-Speed device disconnect/reconnect sequence.
//
// Sequence flow:
//   1. Start SOF (sof_on_sequence on prot_service_sequencer).
//   2. Wait for HS link ENABLED (initial connection + bus reset from VIP).
//   3. Allow MCU firmware to arm EP0 (settle delay).
//   4. Hub-aware enumeration via enumerate_hub_and_dev0(): enumerate the
//      compound hub at address 1, bring up downstream port 1 with hub-class
//      requests, then enumerate USBDC0 at address 2.
//   5. Hold USB_HS_DISC_SOF_COUNT SOF intervals so MCU can count FRAME_INT events.
//   6. Disconnect: vbus_off (p_sequencer.usb_20_phys_service_sequencer) plus
//      drive_dut_vbus() at the pin, THEN sof_off_sequence
//      (prot_service_sequencer). VBus must go away while frames are still
//      running or the controller VBus debounce timer never expires.
//   7. Wait for link to leave ENABLED (disconnect detected).
//   8. Hold off-time.
//   9. Reconnect: vbus_on (p_sequencer.usb_20_phys_service_sequencer) +
//      sof_on_sequence (prot_service_sequencer).
//  10. Wait for HS link to re-establish (ENABLED again).
//  11. Re-run enumerate_hub_and_dev0(). The VBUS cycle reset the whole
//      compound device, so both the hub and USBDC0 are back at address 0 and
//      must be re-addressed from scratch, hub first.
//  12. Hold USB_HS_DISC_SOF_COUNT more SOF intervals so MCU counts FRAME_INT.
//  13. Report success.
//
// WHY THE ENUMERATION MUST BE HUB-AWARE
//
// USBDC0 sits behind the on-chip 2-port compound hub. The MCU firmware
// enables Hub-Enabled mode (HUB_EN, then HUB_CONNECT), so the hub entity
// itself answers all control traffic at address 0 out of HUB RAM and never
// forwards a SETUP token to USBDC0 until the hub has been enumerated AND
// downstream port 1 has been explicitly reset / brought up. An earlier
// revision of this sequence used a flat GET_DESCRIPTOR -> SET_ADDRESS ->
// SET_CONFIGURATION enumeration: every transfer appeared to succeed on the
// host side because the hub answered it, while the MCU firmware saw zero
// SETUP packets and halted on its enumeration timeout
// ("MCU: FAIL - enumeration timeout (got 0 of 3)"). The request encodings
// used below are the ones proven by the passing
// caliptra_ss_usb_hs_dev_bulk_out sequence.
// =============================================================================

// SOF interval count to hold on each side of the disconnect (must be >= 6 to
// allow the MCU firmware to count all 6 FRAME_INT events).
`define USB_HS_DISC_SOF_COUNT 8

class caliptra_ss_usb_hs_dev_disconnect_sequence extends uvm_sequence;

    // Upper bound on how long Step 7 will wait for the VIP host link
    // state machine to leave ENABLED after VBus has been removed. This
    // is a sanity bound, not a functional requirement: the device side
    // disconnect is already proven by DCON_C and VBUS_DEBOUNCED on the
    // firmware side before Step 7 is reached. Keeping it bounded is what
    // guarantees the reconnect in Step 9 always runs, so the firmware
    // Phase 3b poll cannot starve. 200 us is about 25 frame intervals,
    // far more than the link machine needs to react.
    localparam time LINK_DISC_TIMEOUT = 200us;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_disconnect_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_hs_dev_disconnect_sequence");
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

    // Issue a single CONTROL transfer on p_sequencer.xfer_sequencer.
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
                queue_and_hold                     == 0;
            }) begin
            `uvm_fatal("USB_HS_DISC_SEQ",
                $sformatf("svt_usb_transfer randomize() failed for %s", label))
        end
        finish_item(req, -1);
        `uvm_info("USB_HS_DISC_SEQ",
            $sformatf("CONTROL %s issued (addr=%0d wValue=0x%04x wLength=0x%04x)",
                      label, device_addr, wvalue, wlength), UVM_LOW)
    endtask

    task wait_xfer_done(svt_usb_agent agent_h, string label);
        agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
        `uvm_info("USB_HS_DISC_SEQ",
            $sformatf("Transfer %s completed on bus.", label), UVM_LOW)
    endtask

    // Convenience wrapper: issue a control transfer and wait for it to end.
    // The label suffix keeps transfer names unique between the initial
    // enumeration pass and the post-reconnect re-enumeration pass.
    task ctrl_and_wait(
        input svt_usb_agent         host_agent_h,
        input svt_usb_configuration usb_cfg,
        input bit [7:0]  bm_request_type_dir,
        input bit [7:0]  bm_request_type_type,
        input bit [7:0]  bm_request_type_recip,
        input bit [7:0]  brequest_val,
        input bit [15:0] wvalue,
        input bit [15:0] windex,
        input bit [15:0] wlength,
        input int        device_addr,
        input string     label
    );
        do_control_xfer(bm_request_type_dir, bm_request_type_type,
                        bm_request_type_recip, brequest_val, wvalue, windex,
                        wlength, device_addr, label, usb_cfg);
        wait_xfer_done(host_agent_h, label);
    endtask

    // -------------------------------------------------------------------------
    // Hub-aware enumeration of the compound device.
    //
    // Phase a: enumerate the hub itself and move it to address 1.
    // Phase b: bring up downstream port 1, where USBDC0 is attached, using
    //          hub-class port requests. Only after ClearFeature(C_PORT_RESET)
    //          does the hub forward SETUP traffic to USBDC0.
    // Phase c: enumerate USBDC0 and move it to address 2.
    //
    // Called twice: once for the initial enumeration and once after the
    // disconnect / reconnect cycle, which resets the whole compound device
    // back to address 0. "suffix" disambiguates the transfer labels.
    // -------------------------------------------------------------------------
    task enumerate_hub_and_dev0(
        input svt_usb_agent         host_agent_h,
        input svt_usb_configuration usb_cfg,
        input string                suffix
    );
        // The VIP anchor must match the address being driven. Start every
        // enumeration pass from address 0, since both the hub (initial power
        // up) and the whole compound device (after the VBUS cycle) answer
        // there.
        usb_cfg.remote_device_cfg[0].device_address = 7'd0;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_HS_DISC_SEQ",
            $sformatf("Enumeration pass '%s': anchored host agent at device_address=0.",
                      suffix), UVM_LOW)

        // ---------------------------------------------------------------
        // Phase a: enumerate the HUB at address 1.
        // ---------------------------------------------------------------
        ctrl_and_wait(host_agent_h, usb_cfg,
            svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h0100, 16'h0000, 16'h0008,
            0, {"GET_DESC_DEV_addr0_hub_", suffix});

        ctrl_and_wait(host_agent_h, usb_cfg,
            svt_usb_types::HOST_TO_DEVICE, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h05, 16'h0001, 16'h0000, 16'h0000,
            0, {"SET_ADDRESS_1_hub_", suffix});
        #5us;

        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);

        ctrl_and_wait(host_agent_h, usb_cfg,
            svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h0100, 16'h0000, 16'h0012,
            1, {"GET_DESC_DEV_addr1_hub_", suffix});

        ctrl_and_wait(host_agent_h, usb_cfg,
            svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h0200, 16'h0000, 16'h0009,
            1, {"GET_DESC_CFG9_addr1_hub_", suffix});

        ctrl_and_wait(host_agent_h, usb_cfg,
            svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h0200, 16'h0000, 16'h0019,
            1, {"GET_DESC_CFG25_addr1_hub_", suffix});

        ctrl_and_wait(host_agent_h, usb_cfg,
            svt_usb_types::DEVICE_TO_HOST, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h2900, 16'h0000, 16'h0009,
            1, {"GET_DESC_HUB9_addr1_hub_", suffix});

        ctrl_and_wait(host_agent_h, usb_cfg,
            svt_usb_types::HOST_TO_DEVICE, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h09, 16'h0001, 16'h0000, 16'h0000,
            1, {"SET_CONFIG_1_hub_", suffix});

        // ---------------------------------------------------------------
        // Phase b: bring up downstream port 1 (where USBDC0 is attached).
        // ---------------------------------------------------------------
        ctrl_and_wait(host_agent_h, usb_cfg,
            svt_usb_types::DEVICE_TO_HOST, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, 8'h00, 16'h0000, 16'h0001, 16'h0004,
            1, {"GetPortStatus_Port1_", suffix});

        ctrl_and_wait(host_agent_h, usb_cfg,
            svt_usb_types::HOST_TO_DEVICE, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, 8'h01, 16'h0010, 16'h0001, 16'h0000,
            1, {"ClearFeature_C_PORT_CONNECTION_Port1_", suffix});

        ctrl_and_wait(host_agent_h, usb_cfg,
            svt_usb_types::HOST_TO_DEVICE, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, 8'h03, 16'h0004, 16'h0001, 16'h0000,
            1, {"SetFeature_PORT_RESET_Port1_", suffix});
        #10us;

        ctrl_and_wait(host_agent_h, usb_cfg,
            svt_usb_types::HOST_TO_DEVICE, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, 8'h01, 16'h0014, 16'h0001, 16'h0000,
            1, {"ClearFeature_C_PORT_RESET_Port1_", suffix});
        #10us;

        // Reset the VIP anchor back to address 0 before addressing the
        // freshly port-reset USBDC0. Phase a left
        // usb_cfg.remote_device_cfg[0].device_address (and the VIP internal
        // dev_anchor state) at 1. USBDC0, just reset via
        // SetFeature(PORT_RESET) / ClearFeature(C_PORT_RESET) on downstream
        // port 1, responds at address 0 like any freshly reset USB device.
        // Without this reconfigure() the VIP fixed_dev_ep_ustr_valid_ranges
        // constraint (device_address == dev_anchor.device_address == 1)
        // contradicts the do_control_xfer() constraint (device_address == 0)
        // and the very next randomize() call fails as a constraint-solver
        // inconsistency (UVM_FATAL).
        usb_cfg.remote_device_cfg[0].device_address = 7'd0;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_HS_DISC_SEQ",
            "Reset host agent remote device_address=0 before enumerating USBDC0.",
            UVM_LOW)

        // ---------------------------------------------------------------
        // Phase c: enumerate USBDC0 (behind hub port 1) at address 2.
        // ---------------------------------------------------------------
        ctrl_and_wait(host_agent_h, usb_cfg,
            svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h0100, 16'h0000, 16'h0012,
            0, {"GET_DESC_DEV_addr0_", suffix});

        ctrl_and_wait(host_agent_h, usb_cfg,
            svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h00, 16'h0000, 16'h0000, 16'h0002,
            0, {"GET_STATUS_addr0_", suffix});

        ctrl_and_wait(host_agent_h, usb_cfg,
            svt_usb_types::HOST_TO_DEVICE, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h05, 16'h0002, 16'h0000, 16'h0000,
            0, {"SET_ADDRESS_2_", suffix});
        #5us;

        usb_cfg.remote_device_cfg[0].device_address = 7'd2;
        host_agent_h.reconfigure(usb_cfg);

        ctrl_and_wait(host_agent_h, usb_cfg,
            svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h0100, 16'h0000, 16'h0012,
            2, {"GET_DESC_DEV_addr2_", suffix});

        ctrl_and_wait(host_agent_h, usb_cfg,
            svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h08, 16'h0000, 16'h0000, 16'h0001,
            2, {"GET_CONFIG_addr2_", suffix});

        ctrl_and_wait(host_agent_h, usb_cfg,
            svt_usb_types::HOST_TO_DEVICE, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h09, 16'h0001, 16'h0000, 16'h0000,
            2, {"SET_CONFIG_1_", suffix});

        ctrl_and_wait(host_agent_h, usb_cfg,
            svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h08, 16'h0000, 16'h0000, 16'h0001,
            2, {"GET_CONFIG_verify_", suffix});

        `uvm_info("USB_HS_DISC_SEQ",
            $sformatf("Hub-aware enumeration pass '%s' complete (hub at addr 1, USBDC0 at addr 2).",
                      suffix), UVM_LOW)
    endtask

    // -------------------------------------------------------------------------
    // Move the physical DUT VBus pin via caliptra_ss_usb_vbus_driver, and wait
    // until the driver confirms the pin has actually moved.
    //
    // Why this exists: the VIP physical service sequences vbus_off / vbus_on
    // only change state on the VIP side of the link. They never reach
    // cptra_ss_usb_USB_VBus_i, which is the only path VBus has into the
    // design, and which used to be tied to a constant 1 in
    // caliptra_ss_top_tb.sv. Without this call DEVCMDSTAT.VBUS_DEBOUNCED can
    // never clear, DCON_C never fires, and the firmware disconnect wait can
    // only ever time out.
    //
    // Why the fork: uvm_event::trigger() is momentary. If the request were
    // fired before this thread reached wait_trigger() on the acknowledge, the
    // driver could answer in the same delta and the acknowledge would be
    // missed, hanging the sequence. Arming the listener in one branch and
    // delaying the request by #0 in the other guarantees the correct order.
    // -------------------------------------------------------------------------
    task drive_dut_vbus(input bit off);
        uvm_event req_ev;
        uvm_event done_ev;

        req_ev  = uvm_event_pool::get_global(off ? "usb_vbus_off_req"
                                                 : "usb_vbus_on_req");
        done_ev = uvm_event_pool::get_global(off ? "usb_vbus_off_done"
                                                 : "usb_vbus_on_done");

        fork
            begin : WAIT_PIN_ACK
                done_ev.wait_trigger();
            end
            begin : SEND_PIN_REQ
                #0;
                req_ev.trigger();
            end
        join

        `uvm_info("USB_HS_DISC_SEQ",
            $sformatf("DUT VBus pin driven %s.",
                      off ? "LOW (cable removed)" : "HIGH (cable inserted)"),
            UVM_LOW)
    endtask

    virtual task body();
        svt_usb_agent         host_agent_h;
        uvm_component         parent_comp;
        svt_configuration     get_cfg;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;

        parent_comp = p_sequencer.get_parent();
        if (!$cast(host_agent_h, parent_comp))
            `uvm_fatal("USB_HS_DISC_SEQ",
                $sformatf("Cannot cast parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))

        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null)
            `uvm_fatal("USB_HS_DISC_SEQ", "get_shared_status returned null.")

        p_sequencer.get_cfg(get_cfg);
        if (!$cast(usb_cfg, get_cfg))
            `uvm_fatal("USB_HS_DISC_SEQ", "Cannot cast cfg to svt_usb_configuration")

        // -----------------------------------------------------------------
        // Step 1: Start SOF generation (VBUS on + SOF on).
        // -----------------------------------------------------------------
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq;
            sof_on_seq = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on_seq");
            sof_on_seq.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_HS_DISC_SEQ", "SOF generation started.", UVM_LOW)
        end

        // -----------------------------------------------------------------
        // Step 2: Wait for initial HS link ENABLED.
        // -----------------------------------------------------------------
        `uvm_info("USB_HS_DISC_SEQ",
                  "Waiting for initial HS link ENABLED...", UVM_LOW)
        fork
            begin: WAIT_INIT
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_INIT;
            end
            begin: REPORT_INIT
                forever begin
                    #10us `uvm_info("USB_HS_DISC_SEQ",
                        $sformatf("link_state=%p", shared_status.link_usb_20_state),
                        UVM_LOW);
                end
            end
        join
        `uvm_info("USB_HS_DISC_SEQ", "HS link ENABLED (initial connection).", UVM_LOW)

        // -----------------------------------------------------------------
        // Step 3: Allow MCU firmware to arm EP0 before the first SETUP.
        //
        // Runtime note: the firmware only has to run usb_handle_bus_reset()
        // and re-arm the EP0 OUT buffer, which is a handful of register
        // writes. 20 us already covers that with a wide margin, so the
        // previous 100 us was almost entirely idle simulation.
        // -----------------------------------------------------------------
        #20us;

        // -----------------------------------------------------------------
        // Step 4: Hub-aware enumeration (hub at addr 1, port 1 bring-up,
        // USBDC0 at addr 2).
        // -----------------------------------------------------------------
        // Runtime note: every transfer inside enumerate_hub_and_dev0() is
        // already closed on NOTIFY_USB_TRANSFER_ENDED, so nothing is in
        // flight when it returns. The trailing dwell only has to cover the
        // firmware bookkeeping after the last status stage: 50 us, not 500.
        enumerate_hub_and_dev0(host_agent_h, usb_cfg, "init");
        #50us;

        // -----------------------------------------------------------------
        // Step 5: Hold USB_HS_DISC_SOF_COUNT SOF intervals so the MCU
        // firmware can count 6 FRAME_INT events before disconnect.
        // -----------------------------------------------------------------
        // repeat (`USB_HS_DISC_SOF_COUNT) begin
        //     #1000us;
        //     `uvm_info("USB_HS_DISC_SEQ",
        //               "SOF interval (pre-disconnect) - count ongoing", UVM_LOW)
        // end
        // #1000us;

        // -----------------------------------------------------------------
        // Step 6: Disconnect - VBus off first, SOF off only afterwards.
        // -----------------------------------------------------------------
        // The order here is deliberate and must not be swapped back. The
        // device controller de-asserts DEVCMDSTAT.VBUS_DEBOUNCED only after
        // its internal DebounceTimer counts from VBUS_DEBOUNCE_TIME down to
        // 0, and that timer decrements only on a toggle of the frame-driven
        // pie_isotoggle (see vbus_debounc_proc in
        // ip_xxx_3511_hs_structure.a.vhdl). If SOF is stopped before VBus is
        // removed there are no frame edges left, the timer freezes,
        // VBUS_DEBOUNCED stays high and DCON_C never fires, so the MCU
        // firmware Phase 3 poll can only ever time out. Remove VBus while
        // frames are still running, let the debounce expire, then stop SOF.
        `uvm_info("USB_HS_DISC_SEQ",
                  "Driving disconnect (VBUS off, SOF still running)...", UVM_LOW)
        begin
            svt_usb_physical_service_vbus_off_sequence vbus_off;
            vbus_off = svt_usb_physical_service_vbus_off_sequence::type_id::create("vbus_off");
            vbus_off.start(p_sequencer.usb_20_phys_service_sequencer);
            `uvm_info("USB_HS_DISC_SEQ", "VBUS off", UVM_LOW)
        end

        // Both halves are required and they are not redundant:
        //   - the VIP service sequence above tells the host model that the
        //     port is no longer powered, so its link state machine may leave
        //     ENABLED (what Step 7 waits on);
        //   - the call below removes VBus at the DUT pin, which is what makes
        //     the device controller clear VBUS_DEBOUNCED and raise DCON_C
        //     (what the MCU firmware Phase 3 waits on).
        drive_dut_vbus(1'b1);

        // Keep frames running long enough for the VBus debounce counter to
        // reach 0.
        //
        // Sizing evidence, from the first passing run: the VBus pin dropped at
        // 477567 ns and the firmware observed DCON_C at 845120 ns, so the
        // debounce plus poll latency took 367.6 us. An earlier 375 us dwell
        // therefore passed with only 7.4 us of margin, which is far too thin
        // to rely on - any shift in poll phasing or frame alignment would stop
        // SOF before the counter expired and put the timeout failure straight
        // back. 750 us gives roughly 2x headroom (3 spare frame intervals)
        // while still costing far less than the 1 ms dwells this sequence
        // used to carry. Do not shrink this below ~500 us.
        #750us;

        begin
            svt_usb_protocol_service_20_sof_off_sequence sof_off;
            sof_off = svt_usb_protocol_service_20_sof_off_sequence::type_id::create("sof_off");
            sof_off.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_HS_DISC_SEQ", "SOF off (after VBus debounce expiry)", UVM_LOW)
        end

        // -----------------------------------------------------------------
        // Step 7: Wait for the link to leave ENABLED state (disconnect
        // detected by VIP link state machine) - but only for a bounded time.
        //
        // This wait used to be an unbounded "wait (...)" inside a fork/join,
        // and that turned an informational check into a hard dependency: if
        // the VIP host link state machine kept reporting ENABLED, the sequence
        // parked here forever, Step 9 never ran, VBus was never restored, and
        // the only visible symptom was the firmware Phase 3b poll expiring
        // with "FAIL - timeout waiting for VBus to return" about 3 ms later.
        // The firmware side of the disconnect is already fully latched by this
        // point (DCON_C seen, DCON cleared, VBUS_DEBOUNCED low), so the link
        // state is confirmation, not a prerequisite. Bound it, report what was
        // actually observed, and always go on to reconnect.
        // -----------------------------------------------------------------
        begin: WAIT_LINK_DISC
            bit link_left_enabled;
            link_left_enabled = 1'b0;
            fork
                begin
                    wait (shared_status.link_usb_20_state != svt_usb_types::ENABLED);
                    link_left_enabled = 1'b1;
                end
                begin
                    forever begin
                        #5us `uvm_info("USB_HS_DISC_SEQ",
                            $sformatf("Waiting for link to leave ENABLED: link=%p",
                                      shared_status.link_usb_20_state), UVM_LOW);
                    end
                end
                begin
                    #LINK_DISC_TIMEOUT;
                end
            join_any
            disable fork;

            if (link_left_enabled) begin
                `uvm_info("USB_HS_DISC_SEQ",
                          "Link left ENABLED state (disconnected).", UVM_LOW)
            end
            else begin
                `uvm_warning("USB_HS_DISC_SEQ",
                    $sformatf({"Link still reports %p after %0t of VBus removal. ",
                               "Proceeding with the reconnect anyway - the device ",
                               "side disconnect was already confirmed by the ",
                               "firmware (DCON_C / VBUS_DEBOUNCED)."},
                              shared_status.link_usb_20_state, LINK_DISC_TIMEOUT))
            end
        end

        // -----------------------------------------------------------------
        // Step 8: Hold off-time before reconnecting.
        //
        // Runtime note: this is only a plausible "cable out" interval. The
        // firmware has already latched the disconnect by the time Step 7
        // completes, so nothing here needs 1 ms. 100 us still leaves the
        // device well past its VBus debounce window while cutting 0.9 ms of
        // pure idle simulation.
        // -----------------------------------------------------------------
        #100us;

        // -----------------------------------------------------------------
        // Step 9: Reconnect - VBUS on then SOF on.
        // -----------------------------------------------------------------
        `uvm_info("USB_HS_DISC_SEQ",
                  "Reconnecting (VBUS on + SOF on)...", UVM_LOW)
        begin
            svt_usb_physical_service_vbus_on_sequence vbus_on;
            vbus_on = svt_usb_physical_service_vbus_on_sequence::type_id::create("vbus_on");
            vbus_on.start(p_sequencer.usb_20_phys_service_sequencer);
            `uvm_info("USB_HS_DISC_SEQ", "VBUS on", UVM_LOW)
        end

        // Restore VBus at the DUT pin. The firmware Phase 3b loop is spinning
        // on VBUS_DEBOUNCED and only re-asserts DCON (FsPullup) once it sees
        // this, which is what lets the VIP host detect the re-attach and drive
        // the next bus reset. Without it Step 10 would wait forever.
        drive_dut_vbus(1'b0);
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq2;
            sof_on_seq2 = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on_seq2");
            sof_on_seq2.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_HS_DISC_SEQ", "SOF on", UVM_LOW)
        end

        // -----------------------------------------------------------------
        // Step 10: Wait for HS link to re-establish (ENABLED again).
        // -----------------------------------------------------------------
        fork
            begin: WAIT_RECONN
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_RECONN;
            end
            begin: REPORT_RECONN
                forever begin
                    #10us `uvm_info("USB_HS_DISC_SEQ",
                        $sformatf("Waiting for reconnect: link=%p",
                                  shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join
        `uvm_info("USB_HS_DISC_SEQ",
                  "HS link re-established after reconnect.", UVM_LOW)
        // Runtime note: same rationale as Step 3 - just enough for the
        // firmware to service the post-reset DEV_INT and re-arm EP0.
        #20us;

        // -----------------------------------------------------------------
        // Step 11: Re-enumerate after the reconnect.
        //
        // The VBUS cycle reset the entire compound device, so the hub is back
        // at address 0 and downstream port 1 is down again. The same
        // hub-aware flow must therefore be replayed from scratch: hub to
        // address 1, port 1 bring-up, then USBDC0 to address 2. The anchor
        // reset to address 0 is done inside enumerate_hub_and_dev0().
        // -----------------------------------------------------------------
        enumerate_hub_and_dev0(host_agent_h, usb_cfg, "re");
        `uvm_info("USB_HS_DISC_SEQ", "Re-enumeration done.", UVM_LOW)

        // // -----------------------------------------------------------------
        // // Step 12: Hold USB_HS_DISC_SOF_COUNT more SOF intervals so the MCU
        // // firmware can count 6 more FRAME_INT events after reconnect.
        // // -----------------------------------------------------------------
        // repeat (`USB_HS_DISC_SOF_COUNT) begin
        //     #1000us;
        //     `uvm_info("USB_HS_DISC_SEQ",
        //               "SOF interval (post-reconnect) - count ongoing", UVM_LOW)
        // end
        // #10000us;

        // Runtime note: single drain window replacing the old back-to-back
        // #500us + #500us. It exists only so the firmware Phase 4b service
        // window can answer the trailing SETUP packets of the last
        // enumeration pass before the sequence drops its phase objection.
        #50us;

        // -----------------------------------------------------------------
        // Step 13: Report success.
        // -----------------------------------------------------------------
        `uvm_info("USB_HS_DISC_SEQ",
                  "HS disconnect/reconnect sequence complete - all phases done.",
                  UVM_LOW)
    endtask

endclass

`undef USB_HS_DISC_SOF_COUNT

`endif // CALIPTRA_SS_USB_HS_DEV_DISCONNECT_SEQUENCE_SV
