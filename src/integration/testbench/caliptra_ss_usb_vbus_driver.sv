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
//
// -------------------------------------------------------------------------
// caliptra_ss_usb_vbus_driver
//
// Purpose
//   Own the DUT VBus / SessEnd input pins so that a test can model cable
//   removal (VBus going away) instead of only asking the VIP to change its
//   own internal link state.
//
//   cptra_ss_usb_USB_VBus_i is the only path VBus has into the design
//   (caliptra_ss_top.sv port -> ip_xxx_3511_hs_mem_compound_wrapper USB_VBus).
//   It used to be a constant tie-off in caliptra_ss_top_tb.sv:
//
//       assign cptra_ss_usb_USB_VBus_i = 1'b1;
//       assign cptra_ss_usb_sessend_i  = 1'b0;
//
//   With a constant 1 the device controller can never observe VBus removal:
//   DEVCMDSTAT.VBUS_DEBOUNCED can never clear and the DCON_C change bit can
//   never fire. The caliptra_ss_usb_hs_dev_disconnect firmware waits for
//   exactly that condition, so it could only ever spin out its poll timeout
//   and print "MCU: FAIL - timeout waiting for disconnect".
//
// Architecture: the VIP owns VBus
//   The DUT pin follows the VIP UTMI VbusValid / SessEnd outputs, so a single
//   svt_usb_physical_service_vbus_off_sequence moves both the VIP link state
//   machine and the DUT pin. There is one source of truth and the two cannot
//   desynchronise.
//
//   This is also physically correct. A USB device never sources VBus; it only
//   senses the 5 V rail the host supplies through the cable. Ownership of VBus
//   therefore belongs to the host model, which makes it a property of the
//   testbench rather than of any one test.
//
//   The same wiring is what the reference testbench in
//   nxg21179/BITBUCKET_USB_HUB_WS_Aug26 does, via a direct
//       assign cptra_ss_usb_USB_VBus_i = utmi_dut_mac_if.VbusValid;
//
//   This used to be selectable at run time with +usb_vip_vbus, alongside an
//   alternative mode in which stimulus drove the pin directly over uvm_events.
//   That second mode existed only because it was unclear whether the VIP
//   actually drives VbusValid in this non-OTG, device-DUT / VIP-host topology:
//   the DesignWare VIP source under $DESIGNWARE_HOME is not readable here, and
//   the USB UVM User Guide Y-2026.06 mentions VbusValid only in Table 29 "OTG
//   Link Interface Signals". Releasing the testbench tie-off settled it - the
//   VIP does drive the net - so the mode selection has been removed and this
//   behaviour is now the unconditional default. See
//   docs/usb_vip_vbus_ownership.md.
//
// Why the VIP signals are sampled rather than wired straight through
//   A direct readback puts whatever the interface resolves to onto a DUT power
//   input. If the VIP ever stops driving, that is X or Z, which is a far worse
//   failure than the timeout this replaced: it stalls the DUT controller
//   power-up sequence with no obvious cause. So the VIP signals are sampled,
//   and:
//     - a clean 0 or 1 is passed through;
//     - X or Z leaves the pin at the last known-good value, and the module
//       reports once, at UVM_LOW, that the VIP is not driving.
//   The DUT therefore never sees X on a power input regardless of how the VIP
//   behaves, and the run log states plainly what actually happened.
//
// Interface
//   vbus            drives cptra_ss_usb_USB_VBus_i
//   sessend         drives cptra_ss_usb_sessend_i
//   vip_vbus_valid  observes usb_20_mac_if.utmi_dut_mac_if.VbusValid
//   vip_sessend     observes usb_20_mac_if.utmi_dut_mac_if.SessEnd
//
//   SessEnd is tracked separately from VBus, because the VIP may drive
//   VbusValid and leave SessEnd undriven. In that case sessend is forced to
//   ~vbus rather than forwarding X. Session-end asserted is the correct
//   electrical companion to VBus removal: with VBus gone the session really
//   has ended, and holding sessend at 0 would present the controller an
//   inconsistent pair of power inputs.
//
// Handshake
//   Stimulus does not move the pin, but it still needs to know when the pin
//   has moved. Four global uvm_events provide that, following the same
//   convention as caliptra_ss_usb_suspend_resume_checker:
//
//     usb_vbus_off_req   wait until vbus is low  (cable removed)
//     usb_vbus_on_req    wait until vbus is high (cable inserted)
//     usb_vbus_off_done  vbus is now low
//     usb_vbus_on_done   vbus is now high
//
//   A sequence issues the VIP service sequence that actually removes VBus,
//   then waits on the acknowledge, rather than guessing with a delay.
//
//   uvm_event::trigger() is momentary, so the consumer must already be
//   waiting when the producer fires. Both request events are therefore
//   serviced by forever loops that are parked on wait_trigger() from time
//   zero, before any sequence can run.
//
// Ramp time
//   VBus is modelled as an ideal step rather than an RC ramp. The DUT already
//   debounces VBus internally before setting or clearing VBUS_DEBOUNCED, which
//   is the bit firmware actually observes, so adding an analogue ramp here
//   would only add simulation time without changing what the design sees.
// -------------------------------------------------------------------------

// Exact equivalence with the constant tie-off
//   The state variables use declaration initialisers and reach the ports
//   through continuous assigns, rather than being written from an initial
//   block. This matters for one subtle reason: a variable written by an
//   initial block is X until that block executes, which leaves a zero-length
//   delta window at time 0 where the DUT VBus pin would read X, whereas the
//   continuous "assign ... = 1'b1" it replaces had no such window.
//   Declaration initialisers are applied before time 0 simulation begins, so
//   the pins are 1 and 0 from the very first timestep and the replacement is
//   value-identical at every instant, not merely from the first timestep on.
module caliptra_ss_usb_vbus_driver (
    output wire vbus,
    output wire sessend,
    input  wire vip_vbus_valid,
    input  wire vip_sessend
);

    import uvm_pkg::*;

    string MSG_ID = "USB_VBUS_DRV";

    // Global uvm_event names. Must match the strings used in
    // caliptra_ss_usb_hs_dev_disconnect_sequence.svh.
    string VBUS_OFF_REQ_EVENT  = "usb_vbus_off_req";
    string VBUS_ON_REQ_EVENT   = "usb_vbus_on_req";
    string VBUS_OFF_DONE_EVENT = "usb_vbus_off_done";
    string VBUS_ON_DONE_EVENT  = "usb_vbus_on_done";

    uvm_event vbus_off_req;
    uvm_event vbus_on_req;
    uvm_event vbus_off_done;
    uvm_event vbus_on_done;

    // Default state is VBus present, matching the constant tie-off this module
    // replaces. sessend tracks the inverse.
    logic vbus_q    = 1'b1;
    logic sessend_q = 1'b0;

    assign vbus    = vbus_q;
    assign sessend = sessend_q;

    // ---------------------------------------------------------------------
    // Sample the VIP UTMI power signals.
    //
    // A "known" value here means strictly 0 or 1. $isunknown() covers both X
    // and Z, which is exactly the distinction that matters: an undriven
    // svt_usb_if net reads Z, and a multiply-driven one reads X, and neither
    // may be forwarded to a DUT power input.
    //
    // The last known-good value is held in vbus_q / sessend_q, so the pin
    // never has two candidate values and the historical default (1 / 0) is
    // the hold value until the VIP first drives.
    // ---------------------------------------------------------------------
    bit vip_seen_driving;      // VIP has driven a clean value at least once
    bit reported_not_driving;  // one-shot log for the undriven case

    always @(vip_vbus_valid or vip_sessend) begin
        if (!$isunknown(vip_vbus_valid)) begin
            if (!vip_seen_driving) begin
                vip_seen_driving = 1'b1;
                uvm_report_info(MSG_ID,
                    "VIP drives utmi_dut_mac_if.VbusValid with a resolved value. DUT VBus now follows the VIP.",
                    UVM_LOW);
            end
            if (vbus_q !== vip_vbus_valid) begin
                vbus_q = vip_vbus_valid;
                uvm_report_info(MSG_ID,
                    $sformatf("VIP moved VBus: driving USB_VBus=%0b at the DUT pin",
                              vip_vbus_valid),
                    UVM_LOW);
            end
        end else if (!reported_not_driving) begin
            reported_not_driving = 1'b1;
            uvm_report_info(MSG_ID,
                $sformatf("utmi_dut_mac_if.VbusValid reads %0b (X/Z): the VIP is NOT driving it. Holding USB_VBus=%0b so the DUT never sees X on a power input.",
                          vip_vbus_valid, vbus_q),
                UVM_LOW);
        end

        // SessEnd is tracked separately: the VIP may drive VbusValid and
        // leave SessEnd undriven. Fall back to the electrical companion of
        // VBus rather than forwarding X.
        if (!$isunknown(vip_sessend))
            sessend_q = vip_sessend;
        else
            sessend_q = ~vbus_q;
    end

    initial begin
        // Resolve all four handles before waiting on any of them.
        // get_global() creates the event on first use, so whichever side
        // resolves first is irrelevant, but both request events must be parked
        // on wait_trigger() before stimulus starts.
        vbus_off_req  = uvm_event_pool::get_global(VBUS_OFF_REQ_EVENT);
        vbus_on_req   = uvm_event_pool::get_global(VBUS_ON_REQ_EVENT);
        vbus_off_done = uvm_event_pool::get_global(VBUS_OFF_DONE_EVENT);
        vbus_on_done  = uvm_event_pool::get_global(VBUS_ON_DONE_EVENT);

        uvm_report_info(MSG_ID,
            $sformatf("DUT VBus follows the VIP UTMI VbusValid/SessEnd outputs. Requests %s / %s complete once the pin reaches the asked level (acks %s / %s). X/Z on the VIP side is never forwarded to the DUT.",
                      VBUS_OFF_REQ_EVENT, VBUS_ON_REQ_EVENT,
                      VBUS_OFF_DONE_EVENT, VBUS_ON_DONE_EVENT),
            UVM_LOW);

        fork
            forever begin
                vbus_off_req.wait_trigger();
                // The VIP service sequence is what actually removes VBus.
                // Just wait for the pin to get there.
                wait (vbus_q === 1'b0);
                vbus_off_done.trigger();
            end
            forever begin
                vbus_on_req.wait_trigger();
                wait (vbus_q === 1'b1);
                vbus_on_done.trigger();
            end
        join_none
    end

endmodule

// File contains AI-generated response based on internal company sources
