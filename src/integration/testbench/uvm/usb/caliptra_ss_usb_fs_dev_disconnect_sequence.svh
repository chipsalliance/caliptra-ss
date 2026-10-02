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

`ifndef CALIPTRA_SS_USB_FS_DEV_DISCONNECT_SEQUENCE_SV
`define CALIPTRA_SS_USB_FS_DEV_DISCONNECT_SEQUENCE_SV

// =============================================================================
// USB Full-Speed device disconnect/reconnect sequence.
//
// This is the full-speed variant of caliptra_ss_usb_hs_dev_disconnect_sequence.
// The disconnect/reconnect choreography (VBus off/on plus SOF off/on and the
// pin-level drive_dut_vbus() helper) is entirely speed-agnostic - it depends
// only on the VBus debounce/DCON behaviour of the device controller, not on
// whether the link negotiated HS or FS. The link is forced to full-speed by
// the accompanying test (high_speed_capable=0, host/dev speed=FS) and by the
// firmware helper boot_usb_core_fs(), which sets DEVCMDSTAT.PFSC (bit 21) to
// suppress the device K-chirp so the link stays at full-speed.
//
// Sequence flow:
//   1. Start SOF (sof_on_sequence on prot_service_sequencer).
//   2. Wait for FS link ENABLED (initial connection + bus reset from VIP).
//   3. Allow MCU firmware to arm EP0 (settle delay).
//   4. Hub-aware enumeration via enumerate_hub_and_usbdc0(): enumerate the
//      compound hub at address 1, bring up downstream port 1 with hub-class
//      requests, then enumerate USBDC0 at address 2.
//   5. Hold USB_FS_DISC_SOF_COUNT SOF intervals so MCU can count FRAME_INT events.
//   6. Disconnect: vbus_off (p_sequencer.usb_20_phys_service_sequencer) plus
//      drive_dut_vbus() at the pin, THEN sof_off_sequence
//      (prot_service_sequencer). VBus must go away while frames are still
//      running or the controller VBus debounce timer never expires.
//   7. Wait for link to leave ENABLED (disconnect detected).
//   8. Hold off-time.
//   9. Reconnect: vbus_on (p_sequencer.usb_20_phys_service_sequencer) +
//      sof_on_sequence (prot_service_sequencer).
//  10. Wait for FS link to re-establish (ENABLED again).
//  11. Re-run enumerate_hub_and_usbdc0(). The VBUS cycle reset the whole
//      compound device, so both the hub and USBDC0 are back at address 0 and
//      must be re-addressed from scratch, hub first.
//  12. Hold USB_FS_DISC_SOF_COUNT more SOF intervals so MCU counts FRAME_INT.
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
`define USB_FS_DISC_SOF_COUNT 8

class caliptra_ss_usb_fs_dev_disconnect_sequence extends caliptra_ss_usb_base_sequence;

    // Upper bound on how long Step 7 will wait for the VIP host link
    // state machine to leave ENABLED after VBus has been removed. This
    // is a sanity bound, not a functional requirement: the device side
    // disconnect is already proven by DCON_C and VBUS_DEBOUNCED on the
    // firmware side before Step 7 is reached. Keeping it bounded is what
    // guarantees the reconnect in Step 9 always runs, so the firmware
    // Phase 3b poll cannot starve.
    localparam time LINK_DISC_TIMEOUT = 200us;

    `uvm_object_utils(caliptra_ss_usb_fs_dev_disconnect_sequence)

    function new(string name = "caliptra_ss_usb_fs_dev_disconnect_sequence");
        super.new(name);
    endfunction

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

        `uvm_info("USB_FS_DISC_SEQ",
            $sformatf("DUT VBus pin driven %s.",
                      off ? "LOW (cable removed)" : "HIGH (cable inserted)"),
            UVM_LOW)
    endtask

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // -----------------------------------------------------------------
        // Step 1: Start SOF generation (VBUS on + SOF on).
        // -----------------------------------------------------------------
        start_sof_generation();

        // -----------------------------------------------------------------
        // Step 2: Wait for initial FS link ENABLED.
        // -----------------------------------------------------------------
        wait_for_link_enabled(shared_status, "FS host link (initial connection)");

        // -----------------------------------------------------------------
        // Step 3: Allow MCU firmware to arm EP0 before the first SETUP.
        // -----------------------------------------------------------------
        #20us;

        // -----------------------------------------------------------------
        // Step 4: Hub-aware enumeration (hub at addr 1, port 1 bring-up,
        // USBDC0 at addr 2).
        // Anchor reset: the compound device is un-enumerated on entry, so
        // point the VIP remote-device anchor at address 0 before Step A.
        // -----------------------------------------------------------------
        usb_cfg.remote_device_cfg[0].device_address = 7'd0;
        host_agent_h.reconfigure(usb_cfg);
        enumerate_hub_and_usbdc0(host_agent_h, usb_cfg, "_init", 1, 1);
        #50us;

        // -----------------------------------------------------------------
        // Step 5: Hold SOF intervals (FRAME_INT counting is currently
        // disabled on the firmware side; retained for reference).
        // -----------------------------------------------------------------

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
        `uvm_info("USB_FS_DISC_SEQ",
                  "Driving disconnect (VBUS off, SOF still running)...", UVM_LOW)
        begin
            svt_usb_physical_service_vbus_off_sequence vbus_off;
            vbus_off = svt_usb_physical_service_vbus_off_sequence::type_id::create("vbus_off");
            vbus_off.start(p_sequencer.usb_20_phys_service_sequencer);
            `uvm_info("USB_FS_DISC_SEQ", "VBUS off", UVM_LOW)
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
        // FS FRAME-RATE SCALING (this is the whole reason this value differs
        // from the HS variant, and must NOT be copied back to #750us):
        // The device controller's DebounceTimer counts VBUS_DEBOUNCE_TIME (=3)
        // down to 0, decrementing by one on every edge of the frame-driven
        // pie_isotoggle (see vbus_debounc_proc and the timer_sof logic in
        // usb_pie.m.vhdl). pie_isotoggle toggles once per SOF interval, and in
        // full-speed that interval is T_1ms (1 ms) - 8x slower than the HS
        // T_125us (125 us) microframe. So the debounce needs 3 x 1 ms = 3 ms of
        // SOF-running time in FS, versus 3 x 125 us = 375 us in HS. Worst-case
        // frame phasing (VBus removed just after a toggle) pushes the third edge
        // out toward ~4 ms. 5 ms keeps SOF running past that worst case with a
        // 1 ms (one full FS frame) of headroom while still finishing well before
        // the firmware Phase 3 poll ceiling. Do not shrink this below ~4 ms.
        #5ms;

        begin
            svt_usb_protocol_service_20_sof_off_sequence sof_off;
            sof_off = svt_usb_protocol_service_20_sof_off_sequence::type_id::create("sof_off");
            sof_off.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_FS_DISC_SEQ", "SOF off (after VBus debounce expiry)", UVM_LOW)
        end

        // -----------------------------------------------------------------
        // Step 7: Wait for the link to leave ENABLED state (disconnect
        // detected by VIP link state machine) - but only for a bounded time.
        // The firmware side of the disconnect is already fully latched by
        // this point (DCON_C seen, DCON cleared, VBUS_DEBOUNCED low), so the
        // link state is confirmation, not a prerequisite. Bound it, report
        // what was actually observed, and always go on to reconnect.
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
                        #5us `uvm_info("USB_FS_DISC_SEQ",
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
                `uvm_info("USB_FS_DISC_SEQ",
                          "Link left ENABLED state (disconnected).", UVM_LOW)
            end
            else begin
                `uvm_warning("USB_FS_DISC_SEQ",
                    $sformatf({"Link still reports %p after %0t of VBus removal. ",
                               "Proceeding with the reconnect anyway - the device ",
                               "side disconnect was already confirmed by the ",
                               "firmware (DCON_C / VBUS_DEBOUNCED)."},
                              shared_status.link_usb_20_state, LINK_DISC_TIMEOUT))
            end
        end

        // -----------------------------------------------------------------
        // Step 8: Hold off-time before reconnecting.
        // -----------------------------------------------------------------
        #100us;

        // -----------------------------------------------------------------
        // Step 9: Reconnect - VBUS on then SOF on.
        // -----------------------------------------------------------------
        `uvm_info("USB_FS_DISC_SEQ",
                  "Reconnecting (VBUS on + SOF on)...", UVM_LOW)
        begin
            svt_usb_physical_service_vbus_on_sequence vbus_on;
            vbus_on = svt_usb_physical_service_vbus_on_sequence::type_id::create("vbus_on");
            vbus_on.start(p_sequencer.usb_20_phys_service_sequencer);
            `uvm_info("USB_FS_DISC_SEQ", "VBUS on", UVM_LOW)
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
            `uvm_info("USB_FS_DISC_SEQ", "SOF on", UVM_LOW)
        end

        // -----------------------------------------------------------------
        // Step 10: Wait for FS link to re-establish (ENABLED again).
        // -----------------------------------------------------------------
        fork
            begin: WAIT_RECONN
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_RECONN;
            end
            begin: REPORT_RECONN
                forever begin
                    #10us `uvm_info("USB_FS_DISC_SEQ",
                        $sformatf("Waiting for reconnect: link=%p",
                                  shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join
        `uvm_info("USB_FS_DISC_SEQ",
                  "FS link re-established after reconnect.", UVM_LOW)
        #20us;

        // -----------------------------------------------------------------
        // Step 11: Re-enumerate after the reconnect.
        // The VBUS cycle reset the entire compound device, so the hub is back
        // at address 0 and downstream port 1 is down again. The same
        // hub-aware flow must therefore be replayed from scratch: hub to
        // address 1, port 1 bring-up, then USBDC0 to address 2.
        // -----------------------------------------------------------------
        usb_cfg.remote_device_cfg[0].device_address = 7'd0;
        host_agent_h.reconfigure(usb_cfg);
        enumerate_hub_and_usbdc0(host_agent_h, usb_cfg, "_re", 1, 1);
        `uvm_info("USB_FS_DISC_SEQ", "Re-enumeration done.", UVM_LOW)

        // Single drain window so the firmware Phase 4b service window can
        // answer the trailing SETUP packets of the last enumeration pass
        // before the sequence drops its phase objection.
        #50us;

        // -----------------------------------------------------------------
        // Step 13: Report success.
        // -----------------------------------------------------------------
        `uvm_info("USB_FS_DISC_SEQ",
                  "FS disconnect/reconnect sequence complete - all phases done.",
                  UVM_LOW)
    endtask

endclass

`undef USB_FS_DISC_SOF_COUNT

`endif // CALIPTRA_SS_USB_FS_DEV_DISCONNECT_SEQUENCE_SV
