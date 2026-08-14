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

`ifndef CALIPTRA_SS_USB_HS_HOST_REMOTEWAKEUP_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_HOST_REMOTEWAKEUP_SEQUENCE_SV

// =============================================================================
// USB HS host remote wakeup sequence.
//
// DUT role  : USB HOST  -- ip_3515 host controller (SOC_USBHSH_* registers).
// VIP role  : DEVICE/SERIAL_IF HS agent. Initiates remote wakeup from SUSPEND.
//
// This sequence mirrors the NIOBE usb_hs_host_remotewakeup.cpp flow:
//
//   1. Wait for VIP DEVICE link state RECEIVING_IS (HS idle after chirp).
//      This corresponds to the DUT completing port reset (PR cleared, PSPD=HS).
//
//   2. Start SVT built-in device framework response sequence in background.
//      Handles any EP0 control transfers from the DUT HOST during SOF phase.
//
//   3. Wait for VIP DEVICE to enter SUSPEND state.
//      The MCU firmware disables SOF (USBINTR=0) after 2 SOF events and sets
//      PORTSC1.SUSP. The VIP DEVICE detects 3ms of bus idle (no SOF tokens)
//      and transitions to SUSPEND.
//
//   4. Fire svt_usb_link_service_device_remote_wakeup_sequence on the DEVICE
//      agent link_service_sequencer. This drives a K-state (resume signaling)
//      from the device side -- the device-initiated remote wakeup.
//      (Reference: SVT b2b_phy suspend_remote_wakeup_sequence.sv)
//
//   5. Wait for VIP DEVICE to return to RECEIVING_IS (HS idle after resume).
//      The MCU firmware detects FPR/SUSP cleared and polls 3 post-resume SOFs.
//
//   6. Wait for MCU to complete post-resume SOF polling and halt.
//
// Sequence flow matches NIOBE test:
//   NIOBE: sema_micrf_irq x2 -> suspend -> needclk fall -> deep sleep ->
//          needclk rise (device K-state) -> FPR -> sema_micrf_irq x3
//   Here:  RECEIVING_IS -> SUSPEND -> remote_wakeup_seq -> RECEIVING_IS
//
// VIP topology: same as bulk_out test.
//   Single DEVICE/SERIAL_IF HS agent installed as cfg.host_cfg.
//   nvs_usb_phy bridges DUT HOST MAC UTMI signals to DP/DM serial bus.
// =============================================================================

class caliptra_ss_usb_hs_host_remotewakeup_sequence extends uvm_sequence;
    `uvm_object_utils(caliptra_ss_usb_hs_host_remotewakeup_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_hs_host_remotewakeup_sequence");
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
    // body: main sequence
    // -------------------------------------------------------------------------
    virtual task body();
        svt_usb_agent dev_agent_h;
        uvm_component  parent_comp;

        // -----------------------------------------------------------------------
        // Get the VIP DEVICE agent handle from the sequencer parent.
        // -----------------------------------------------------------------------
        parent_comp = p_sequencer.get_parent();
        if (!$cast(dev_agent_h, parent_comp))
            `uvm_fatal("USB_HS_HOST_RWKUP_SEQ",
                $sformatf("Cannot cast parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))

        if (dev_agent_h.shared_status == null)
            `uvm_fatal("USB_HS_HOST_RWKUP_SEQ", "dev_agent_h.shared_status is null.")

        // -----------------------------------------------------------------------
        // Step 1: Wait for DEVICE link state RECEIVING_IS (HS idle after chirp).
        //
        // After HS chirp completes, the DEVICE link SM enters RECEIVING_IS.
        // This is equivalent to the DUT HOST completing port reset (PR=0, PSPD=HS).
        // Also accept RECEIVING_J in case the VIP falls back to FS idle.
        // Periodic state logging every 10us for debugging.
        // (Reference: bulk_out_sequence step 1, SVT b2b_phy attach example)
        // -----------------------------------------------------------------------
        `uvm_info("USB_HS_HOST_RWKUP_SEQ",
            $sformatf("Waiting for HS link RECEIVING_IS (current=%s)...",
                      dev_agent_h.shared_status.link_usb_20_state.name()), UVM_LOW)
        fork
            begin: WAIT_HS_IDLE
                wait ((dev_agent_h.shared_status.link_usb_20_state ==
                                        svt_usb_types::RECEIVING_IS) ||
                      (dev_agent_h.shared_status.link_usb_20_state ==
                                        svt_usb_types::RECEIVING_J));
                disable REPORT_STATE_1;
            end
            begin: REPORT_STATE_1
                forever begin
                    #10us;
                    `uvm_info("USB_HS_HOST_RWKUP_SEQ",
                        $sformatf("link_state = %s",
                                  dev_agent_h.shared_status.link_usb_20_state.name()),
                        UVM_LOW)
                end
            end
        join

        `uvm_info("USB_HS_HOST_RWKUP_SEQ",
            $sformatf("HS link idle reached (%s). Host is running SOF.",
                      dev_agent_h.shared_status.link_usb_20_state.name()), UVM_LOW)

        // -----------------------------------------------------------------------
        // Force VIP back to HS after BUS_RESET exit (same fix as bulk_out).
        //
        // During ATL port reset, bus transitions SE0->K (ATL SOF SYNC) rather
        // than SE0->J. The VIP bus_reset_state handler may program
        // PERIPHERAL_FULL_SPEED even after chirp KJ succeeded. Reconfigure to
        // HS so the protocol layer can decode HS SOF tokens from the DUT HOST.
        // -----------------------------------------------------------------------
        begin
            svt_configuration        base_cfg;
            svt_usb_agent_configuration recfg;
            dev_agent_h.get_cfg(base_cfg);
            if (!$cast(recfg, base_cfg.clone()))
                `uvm_fatal("USB_HS_HOST_RWKUP_SEQ",
                    "Cannot cast base_cfg clone to svt_usb_agent_configuration")
            recfg.local_device_cfg[0].connected_bus_speed   = svt_usb_types::HS;
            recfg.local_device_cfg[0].high_speed_capable    = 1'b1;
            // Must keep remote_wakeup_capable=1 after reconfigure().
            // reconfigure() clones the config; the clone resets this field to
            // its default (0), overwriting the value set in build_phase.
            recfg.local_device_cfg[0].remote_wakeup_capable = 1'b1;
            dev_agent_h.reconfigure(recfg);
            `uvm_info("USB_HS_HOST_RWKUP_SEQ",
                "Reconfigured VIP device agent to HS with remote_wakeup_capable=1.", UVM_LOW)
        end

        // -----------------------------------------------------------------------
        // Step 2: Start SVT built-in device framework response sequence.
        //
        // Runs in background to handle any EP0 control requests from DUT HOST
        // during the SOF phase before suspend. The framework sequence correctly
        // advances the EP0 state machine for CONTROL transfers (SET_ADDRESS,
        // SET_CONFIGURATION, etc.) using assemble_transfer_response().
        // (Same pattern as bulk_out_sequence.)
        // -----------------------------------------------------------------------
        fork
            begin
                svt_usb_device_framework_standard_request_response_virtual_sequence dev_fw_seq;
                dev_fw_seq =
                    svt_usb_device_framework_standard_request_response_virtual_sequence::type_id::create(
                        "dev_fw_seq");
                dev_fw_seq.start(dev_agent_h.virt_sequencer);
            end
        join_none

        // -----------------------------------------------------------------------
        // Step 3: Wait for VIP DEVICE to enter SUSPEND state.
        //
        // The MCU firmware sets PORTSC1.SUSP and immediately USBCMD=0 to stop
        // SOF generation. With no SOF tokens on the bus, the DP line transitions
        // to J-state (device D+ pull-up dominates once host pull-downs are gone).
        // This J-state is STABLE -- twtrev fires once on the J-state transition
        // and then the bus stays idle. Once twtrev expires (500us), tinactivity
        // starts; after tinactivity (200us) the VIP transitions to SUSPEND.
        // Total time from USBCMD=0 to SUSPEND: ~700us.
        // The MCU spin is ~1ms, so wait(SUSPEND) fires ~300us before MCU restarts.
        //
        // Timer values (set in test build_phase):
        //   twtrev      = 500us  : window after RECEIVING_IS before BUS_RESET.
        //                          Short enough to expire before MCU 1ms spin ends.
        //   tinactivity = 200us  : inactivity timer for SUSPEND entry.
        //                          Starts after twtrev expires.
        //
        // (NIOBE reference: "sema_usb_needclk_fall.get()" -- needclk goes low
        //  when the device has entered suspend and the USB clock can stop.)
        // -----------------------------------------------------------------------
        `uvm_info("USB_HS_HOST_RWKUP_SEQ",
            "Waiting for VIP DEVICE to enter SUSPEND (MCU stopped SOF, twtrev=500us, tinactivity=200us)...",
            UVM_LOW)
        fork
            begin: WAIT_SUSPEND
                wait (dev_agent_h.shared_status.link_usb_20_state ==
                                        svt_usb_types::SUSPEND);
                disable REPORT_STATE_2;
            end
            begin: REPORT_STATE_2
                forever begin
                    #10us;
                    `uvm_info("USB_HS_HOST_RWKUP_SEQ",
                        $sformatf("link_state = %s (waiting for SUSPEND)",
                                  dev_agent_h.shared_status.link_usb_20_state.name()),
                        UVM_LOW)
                end
            end
        join

        `uvm_info("USB_HS_HOST_RWKUP_SEQ",
            $sformatf("VIP DEVICE entered SUSPEND at %0t. Initiating device remote wakeup...",
                      $time),
            UVM_LOW)

        // -----------------------------------------------------------------------
        // Step 4: Drive device-initiated remote wakeup (K-state) from DEVICE agent.
        //
        // svt_usb_link_service_device_remote_wakeup_sequence drives resume K-state
        // on the USB bus from the device side. This wakes up the DUT HOST, which
        // should detect the K-state on its suspended port, assert FPR internally
        // (reflected in PORTSC1.FPR), and set PCD in USBSTS.
        //
        // The MCU firmware then:
        //   - Reads PORTSC1 after USBCMD=RS restart, verifies SUSP still set
        //   - Asserts FPR to continue resume signaling
        //   - Waits ~10ms then writes PORTSC1=PP|PED to end resume
        //
        // (Reference: SVT b2b_phy suspend_remote_wakeup_sequence.sv,
        //  NIOBE: "sema_usb_needclk_rise.get()" -> FPR -> PP|PED)
        // -----------------------------------------------------------------------
        begin
            svt_usb_link_service_device_remote_wakeup_sequence rwkup_seq;
            rwkup_seq =
                svt_usb_link_service_device_remote_wakeup_sequence::type_id::create(
                    "rwkup_seq");
            rwkup_seq.start(dev_agent_h.virt_sequencer.link_service_sequencer);
            `uvm_info("USB_HS_HOST_RWKUP_SEQ",
                "Device remote wakeup sequence started (K-state driven on bus).", UVM_LOW)
        end

        // -----------------------------------------------------------------------
        // Step 5: Wait for VIP DEVICE to return to RECEIVING_IS (HS idle).
        //
        // After the MCU firmware asserts FPR and then writes PP|PED to end
        // resume signaling, the bus returns to HS idle. The VIP DEVICE link
        // state transitions back to RECEIVING_IS.
        //
        // The MCU firmware then polls 3 more SOF_IRQ events to confirm normal
        // microframe traffic and halts.
        //
        // (Reference: SVT b2b_phy suspend_remote_wakeup_sequence.sv:
        //  "wait (host_agent.shared_status.link_usb_20_state == ENABLED) &&
        //   wait (dev_agent.shared_status.link_usb_20_state == RECEIVING_IS)")
        // -----------------------------------------------------------------------
        `uvm_info("USB_HS_HOST_RWKUP_SEQ",
            "Waiting for VIP DEVICE to return to RECEIVING_IS after resume...", UVM_LOW)
        fork
            begin: WAIT_RESUMED
                wait ((dev_agent_h.shared_status.link_usb_20_state ==
                                        svt_usb_types::RECEIVING_IS) ||
                      (dev_agent_h.shared_status.link_usb_20_state ==
                                        svt_usb_types::RECEIVING_J));
                disable REPORT_STATE_3;
            end
            begin: REPORT_STATE_3
                forever begin
                    #10us;
                    `uvm_info("USB_HS_HOST_RWKUP_SEQ",
                        $sformatf("link_state = %s (waiting for RECEIVING_IS)",
                                  dev_agent_h.shared_status.link_usb_20_state.name()),
                        UVM_LOW)
                end
            end
        join

        `uvm_info("USB_HS_HOST_RWKUP_SEQ",
            $sformatf("VIP DEVICE returned to HS idle (%s). Resume complete.",
                      dev_agent_h.shared_status.link_usb_20_state.name()), UVM_LOW)

        // -----------------------------------------------------------------------
        // Step 6: Allow MCU firmware time to complete post-resume SOF polling
        // (3 SOF events at 125us each = ~375us) and print final result.
        // -----------------------------------------------------------------------
        #500us;

        `uvm_info("USB_HS_HOST_RWKUP_SEQ",
            "USB HS host remote wakeup - PASSED.", UVM_LOW)
        `uvm_info("USB_HS_HOST_RWKUP_SEQ",
            "caliptra_ss_usb_hs_host_remotewakeup_sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_HOST_REMOTEWAKEUP_SEQUENCE_SV
