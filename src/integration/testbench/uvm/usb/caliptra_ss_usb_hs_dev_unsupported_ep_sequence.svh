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

`ifndef CALIPTRA_SS_USB_HS_DEV_UNSUPPORTED_EP_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_UNSUPPORTED_EP_SEQUENCE_SV

// =============================================================================
// USB High-Speed "token to an UNSUPPORTED endpoint" sequence (Hub-Enabled).
//
// Minimal directed test. After enumeration the host sends ONE 8-byte BULK OUT
// to an endpoint number that has no physical endpoint behind it in this
// configuration. The device must not respond at all: no ACK, no NAK, no STALL.
//
// Endpoint number derivation (ground truth, src/integration/rtl/
// caliptra_ss_top.sv):
//   parameter USB_C_DEV0_NBPHYSEP = 28;
//   parameter USB_C_DEV1_NBPHYSEP = 28;
// Both are forwarded into ip_xxx_3511_hs_mem_compound_wrapper.sv as
// .C_DEV0_NBPHYSEP / .C_DEV1_NBPHYSEP and from there into the per-device VHDL
// generic C_NBPHYSEP. Physical endpoints are allocated as OUT/IN pairs, so
// 28 slots = 14 pairs = USB endpoint numbers 1..14 are backed by hardware
// (slot 0/1 being EP0 OUT/IN). Endpoint number 15 is the first one with no
// physical endpoint behind it, and it is still encodable because the RTL type
// t_ep.EPNB has range 0 to 15. EP15 is therefore the probe target.
//
// The verdict comes from caliptra_ss_usb_handshake_counter_callback, which
// counts device-sourced ACK/NAK/STALL packets on the host link monitor while
// its window is armed. The VIP's own transfer-level timeout is deliberately
// NOT the verdict (a timeout is also what a broken testbench looks like) and
// is demoted to informational by the inline report catcher below.
//
// No positive-control phase is needed: enumeration itself has already produced
// device handshakes through the same link monitor, so the measurement path is
// known to be alive before the probe runs.
//
// Only an OUT endpoint is probed. An IN token to an endpoint with no responder
// does not terminate cleanly in the VIP (hung sim, see
// claude_md/22_usb_hub_endpoint_halt.md) and would add no RTL coverage.
// =============================================================================

// Bytes per probe transfer. Deliberately one short HS bulk packet.
`define USB_HS_UNSUPPORTED_EP_BYTES 8

// Bus-silence observation window, in microseconds. Generous relative to the
// ~200 ns a handshake would take to come back, but short enough that the run
// does not depend on the VIP device_timeout expiring.
`define USB_HS_UNSUPPORTED_EP_SILENCE_US 200

// Probe endpoint number: first endpoint with no physical endpoint behind it
// for C_DEV0_NBPHYSEP / C_DEV1_NBPHYSEP = 28 (see the header comment).
`define USB_HS_UNSUPPORTED_EP_NUM 15

// USB device address of the probe target. The hub takes address 1 and the
// device enumerated behind the active downstream port takes address 2. Used
// both for do_data_xfer() and for the report-catcher signature match, so the
// two can never drift apart.
`define USB_HS_UNSUPPORTED_EP_DEV_ADDR 2

// -----------------------------------------------------------------------------
// Scoped report catcher: the host VIP legitimately complains here, because
// silence is exactly what we asked for. A non-responding endpoint produces TWO
// distinct families of expected reports, and both must be demoted:
//
//   1. transfer/protocol level, on uvm_test_top.env.host_agent.prot:
//        "Unexpected Device Timeout <Dev:2 EP:15 BULK_OUT_TRANSFER>"
//      Matched on the message by the exact probe signature
//      "*Device Timeout*Dev:<addr>*EP:<num>*BULK_OUT*", built from the
//      DEV_ADDR / EP_NUM macros above.
//
//   2. link level, on uvm_test_top.env.host_agent.link, id
//      "register_fail:LINK 20 TIMING CHECKS:COMMON:tend_to_end_delay_check":
//        "... Maximum End-to-end Signal Delay - Response packet not received
//         within the expiry of End to End Delay Timer."
//      Matched on the id by "*tend_to_end_delay_check*" only. The text
//      contains neither "timeout" nor "TIMEOUT", so family 1's signature does
//      NOT cover it. This check fires once per VIP token retry (roughly every
//      1.8 us), so it appears many times.
//
// Demote both to UVM_INFO so the intended behavior does not fail the run, while
// keeping the evidence of silence visible in the log.
//
// Three independent guards keep the demotion from swallowing unrelated
// failures:
//   - the reporting component must live inside the host VIP agent
//     (get_client().get_full_name() matches "*host_agent*"), so reports from
//     the test, the environment or the MCU-halt watchdog are never touched;
//   - the report must carry one of the two signatures above - no bare
//     "timeout" / "TIMEOUT" / "End-to-end" text matching, and the broad
//     "TIMING CHECKS" id prefix is deliberately NOT matched, so any other VIP
//     timing violation still fails the run;
//   - the catcher is armed only for the probe window: it is registered right
//     before arm_window() (i.e. after enumeration, so an enumeration timeout
//     stays an UVM_ERROR) and deleted again once the outstanding probe has
//     drained. In particular the base test's "TIMEOUT: MCU did not halt ..."
//     watchdog error is reported after the catcher is gone, and from
//     uvm_test_top, so it can never be demoted.
//
// The alternative knob - widening cfg.host_cfg.tend_to_end_delay_hs in the test
// build_phase, as caliptra_ss_usb_hs_dev1_bulk_loopback_test.svh does with
// 100 ms - was rejected here: it perturbs the VIP timing model for the whole
// run and hides the silence instead of recording it.
// -----------------------------------------------------------------------------

class caliptra_ss_usb_unsupported_ep_timeout_catcher extends uvm_report_catcher;

    static bit armed;

    function new(string name = "caliptra_ss_usb_unsupported_ep_timeout_catcher");
        super.new(name);
    endfunction

    virtual function action_e catch();
        string id_s;
        string msg_s;
        string client_s;
        string probe_sig;

        if (!armed) return THROW;
        if (get_severity() != UVM_ERROR && get_severity() != UVM_FATAL)
            return THROW;

        // Only the host VIP agent may be demoted. Reports from the test, the
        // environment or any other component (for example the base test's
        // MCU-halt watchdog, which reports from uvm_test_top) pass through.
        client_s = (get_client() == null) ? "" : get_client().get_full_name();
        if (!uvm_is_match("*host_agent*", client_s))
            return THROW;

        id_s  = get_id();
        msg_s = get_message();

        // Family 1: transfer/protocol level device-response timeout, matched
        // on the exact probe signature so that a timeout against any other
        // device address, endpoint or transfer kind still fails the run.
        probe_sig = $sformatf("*Device Timeout*Dev:%0d*EP:%0d*BULK_OUT*",
                              `USB_HS_UNSUPPORTED_EP_DEV_ADDR,
                              `USB_HS_UNSUPPORTED_EP_NUM);

        // Family 2: link level end-to-end signal delay timing check, matched
        // on the specific check name only (not the broad "TIMING CHECKS"
        // prefix). Its text never contains "timeout".
        if (!(uvm_is_match(probe_sig,                    msg_s) ||
              uvm_is_match("*tend_to_end_delay_check*",  id_s)))
            return THROW;

        set_severity(UVM_INFO);
        set_verbosity(UVM_LOW);
        set_id("USB_HS_UNSUPPORTED_EP_EXPECTED_SILENCE");
        set_message({"EXPECTED (unsupported endpoint must not respond): ", msg_s});
        return THROW;
    endfunction

endclass

class caliptra_ss_usb_hs_dev_unsupported_ep_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_unsupported_ep_sequence)

    function new(string name = "caliptra_ss_usb_hs_dev_unsupported_ep_sequence");
        super.new(name);
    endfunction

    // Build the 8-byte probe payload. Pattern is incidental; nothing data
    // checks it. Kept non-trivial so it is easy to spot in a waveform.
    protected function void build_probe_payload(ref bit [7:0] data[]);
        data = new[`USB_HS_UNSUPPORTED_EP_BYTES];
        foreach (data[i])
            data[i] = 8'hA0 + i[7:0];
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;
        svt_usb_transfer      probe_req;
        bit [7:0]             probe_data[];
        bit                   xfer_returned;
        int unsigned          hs_count;

        caliptra_ss_usb_handshake_counter_callback      pkt_cb;
        caliptra_ss_usb_unsupported_ep_timeout_catcher  to_catcher;

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: wait for the HS link to come up after the chirp handshake.
        wait_for_link_enabled(shared_status, "HS host link");

        // Step 2: SOF generation, then let the firmware re-arm EP0 post-reset.
        start_sof_generation();
        #20us;

        // Step 3: install the handshake counter on the host link monitor. The
        // window is left disarmed so enumeration handshakes are not counted.
        pkt_cb = caliptra_ss_usb_handshake_counter_callback::type_id::create("pkt_cb");
        uvm_callbacks#(svt_usb_link_monitor, svt_usb_link_monitor_callback)::add(
            host_agent_h.link_mon, pkt_cb);
        caliptra_ss_usb_handshake_counter_callback::disarm_window();

        // Step 4: enumerate the hub at address 1, bring up downstream port 1,
        // then enumerate USBDC0 at address 2 (base-class steps A -> B -> C).
        enumerate_hub_and_usbdc0(host_agent_h, usb_cfg);
        `uvm_info("USB_HS_UNSUPPORTED_EP_SEQ", "HS enumeration complete.", UVM_LOW)
        #10us;

        build_probe_payload(probe_data);

        // ---------------------------------------------------------------------
        // The probe: one BULK OUT to an endpoint number with no physical
        // endpoint behind it. The bus must stay silent.
        // ---------------------------------------------------------------------
        `uvm_info("USB_HS_UNSUPPORTED_EP_SEQ",
                  $sformatf("BULK OUT to UNSUPPORTED EP%0d - NO response is expected.",
                            `USB_HS_UNSUPPORTED_EP_NUM),
                  UVM_LOW)

        // Register and arm the timeout catcher only now. Everything before
        // this point (link bring-up, hub and device enumeration) must still be
        // able to fail the run on a timeout, so the catcher is deliberately
        // not installed any earlier.
        to_catcher = new("unsupported_ep_timeout_catcher");
        caliptra_ss_usb_unsupported_ep_timeout_catcher::armed = 1;
        uvm_report_cb::add(null, to_catcher);

        caliptra_ss_usb_handshake_counter_callback::arm_window();

        xfer_returned = 0;
        fork
            begin
                do_data_xfer(
                    .agent_h            (host_agent_h),
                    .usb_cfg            (usb_cfg),
                    .xfer_kind          (svt_usb_transfer::BULK_OUT_TRANSFER),
                    .device_addr        (`USB_HS_UNSUPPORTED_EP_DEV_ADDR),
                    .ep_num             (`USB_HS_UNSUPPORTED_EP_NUM),
                    .byte_count         (`USB_HS_UNSUPPORTED_EP_BYTES),
                    .ep_anchor_idx      (1),
                    .label              ("HS_UNSUPPORTED_EP_OUT"),
                    .req                (probe_req),
                    .obj_name           ("unsupported_ep_probe_req"),
                    // NOTE: do not set no_zero_length_end here. On HS the bulk
                    // max_packet_size is 512 bytes, so an 8-byte OUT is a
                    // short packet and the VIP forces
                    // aligned_transfer_ends_with_zero_length == 1; asking for
                    // 0 makes the transfer constraints unsatisfiable. A short
                    // packet already terminates the transfer.
                    .payload_data       (probe_data));
                xfer_returned = 1;
            end
            begin
                // Bounded silence window. do_data_xfer always waits for the
                // transfer-ended notification, which by design never arrives
                // here until the VIP device_timeout expires, so this window is
                // what ends the probe.
                #(`USB_HS_UNSUPPORTED_EP_SILENCE_US * 1us);
            end
        join_any
        // "disable fork" is a statement, so it needs its own semicolon.
        // Without it the parser folds the next statement into this one and
        // reports a syntax error on the following line.
        disable fork;

        caliptra_ss_usb_handshake_counter_callback::disarm_window();

        hs_count = caliptra_ss_usb_handshake_counter_callback::get_handshake_count();
        `uvm_info("USB_HS_UNSUPPORTED_EP_SEQ",
                  $sformatf("Handshakes from device: %0d (ACK=%0d NAK=%0d STALL=%0d), xfer_returned=%0d",
                            hs_count,
                            caliptra_ss_usb_handshake_counter_callback::get_ack_count(),
                            caliptra_ss_usb_handshake_counter_callback::get_nak_count(),
                            caliptra_ss_usb_handshake_counter_callback::get_stall_count(),
                            xfer_returned),
                  UVM_LOW)

        if (hs_count != 0)
            `uvm_error("USB_HS_UNSUPPORTED_EP_SEQ",
                $sformatf("The UNSUPPORTED endpoint EP%0d responded. %0d handshake(s) observed (ACK=%0d NAK=%0d STALL=%0d); the expected behavior is no response at all.",
                          `USB_HS_UNSUPPORTED_EP_NUM,
                          hs_count,
                          caliptra_ss_usb_handshake_counter_callback::get_ack_count(),
                          caliptra_ss_usb_handshake_counter_callback::get_nak_count(),
                          caliptra_ss_usb_handshake_counter_callback::get_stall_count()))
        else
            `uvm_info("USB_HS_UNSUPPORTED_EP_SEQ",
                $sformatf("PASSED: bus stayed silent for %0d us after the OUT token to UNSUPPORTED EP%0d.",
                          `USB_HS_UNSUPPORTED_EP_SILENCE_US,
                          `USB_HS_UNSUPPORTED_EP_NUM),
                UVM_LOW)

        // Drain. The catcher stays armed across this delay so the VIP's late
        // device_timeout for the aborted probe transfer cannot fail the run.
        #50us;

        // The probe has drained: remove the catcher so that every later report
        // (in particular the base test's MCU-halt watchdog error) is seen at
        // its original severity.
        caliptra_ss_usb_unsupported_ep_timeout_catcher::armed = 0;
        uvm_report_cb::delete(null, to_catcher);

        `uvm_info("USB_HS_UNSUPPORTED_EP_SEQ",
                  "HS unsupported-endpoint sequence complete.", UVM_LOW)
    endtask

endclass

`undef USB_HS_UNSUPPORTED_EP_BYTES
`undef USB_HS_UNSUPPORTED_EP_SILENCE_US
`undef USB_HS_UNSUPPORTED_EP_NUM
`undef USB_HS_UNSUPPORTED_EP_DEV_ADDR


`endif // CALIPTRA_SS_USB_HS_DEV_UNSUPPORTED_EP_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
