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

`ifndef CALIPTRA_SS_USB_FS_DEV_UNSUPPORTED_EP_SEQUENCE_SV
`define CALIPTRA_SS_USB_FS_DEV_UNSUPPORTED_EP_SEQUENCE_SV

// =============================================================================
// USB Full-Speed "token to an UNSUPPORTED endpoint" sequence (Hub-Enabled).
//
// Full-speed sibling of caliptra_ss_usb_hs_dev_unsupported_ep_sequence.svh.
// The scenario is identical: after enumeration the host sends ONE 8-byte BULK
// OUT to an endpoint number that has no physical endpoint behind it in this
// configuration, and the device must not respond at all - no ACK, no NAK, no
// STALL. Only the wire speed, the packet sizes and the observation delays
// differ (see the FS porting rules in docs/usb/usb_fs_vs_hs_test_porting.md).
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
// t_ep.EPNB has range 0 to 15. EP15 is therefore the probe target. The
// endpoint map is speed independent, so FS uses the same EP15.
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

// Bytes per probe transfer. Deliberately one short FS bulk packet (the FS bulk
// max packet size is 64 bytes, so 8 bytes is a short packet and terminates the
// transfer on its own).
`define USB_FS_UNSUPPORTED_EP_BYTES 8

// Bus-silence observation window, in microseconds. Scaled up from the HS value
// of 200 us: full speed is about 40x slower on the wire and the frame period is
// 1 ms instead of 125 us, so the window must span several FS frames to be the
// same kind of evidence. 1000 us = one full FS frame period of silence, which
// is far longer than the ~1.5 us a handshake would need to come back, while
// still shorter than the 5000 us VIP device_timeout set by the test.
`define USB_FS_UNSUPPORTED_EP_SILENCE_US 1000

// Maximum time the probe may take to reach the wire, in microseconds, counted
// from the moment the transfer is forked. Scaled from the HS value of 50 us by
// the usual FS factor of 8: far more than the post-enumeration latency to the
// first token, and still well inside both the 1000 us silence budget above and
// the 5000 us VIP device_timeout set by the test. If the OUT token / DATA
// packet for the probe is not observed by the link monitor within this time
// the stimulus never happened, which is a missing-stimulus failure and NOT bus
// silence.
`define USB_FS_UNSUPPORTED_EP_STIMULUS_TIMEOUT_US 400

// Probe endpoint number: first endpoint with no physical endpoint behind it
// for C_DEV0_NBPHYSEP / C_DEV1_NBPHYSEP = 28 (see the header comment).
`define USB_FS_UNSUPPORTED_EP_NUM 15

// USB device address of the probe target. The hub takes address 1 and the
// device enumerated behind the active downstream port takes address 2. Used
// both for do_data_xfer() and for the report-catcher signature match, so the
// two can never drift apart.
`define USB_FS_UNSUPPORTED_EP_DEV_ADDR 2

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
//      NOT cover it.
//
// At FS the test build_phase also widens tend_to_end_delay_fs to 2 ms (part of
// the standard FS conversion block), which reduces how often family 2 re-fires
// compared to HS, but it does not remove it: the probe response never arrives,
// so the timer still expires. The catcher is therefore kept as is.
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
// -----------------------------------------------------------------------------

class caliptra_ss_usb_fs_unsupported_ep_timeout_catcher extends uvm_report_catcher;

    static bit armed;

    function new(string name = "caliptra_ss_usb_fs_unsupported_ep_timeout_catcher");
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
                              `USB_FS_UNSUPPORTED_EP_DEV_ADDR,
                              `USB_FS_UNSUPPORTED_EP_NUM);

        // Family 2: link level end-to-end signal delay timing check, matched
        // on the specific check name only (not the broad "TIMING CHECKS"
        // prefix). Its text never contains "timeout".
        if (!(uvm_is_match(probe_sig,                    msg_s) ||
              uvm_is_match("*tend_to_end_delay_check*",  id_s)))
            return THROW;

        set_severity(UVM_INFO);
        set_verbosity(UVM_LOW);
        set_id("USB_FS_UNSUPPORTED_EP_EXPECTED_SILENCE");
        set_message({"EXPECTED (unsupported endpoint must not respond): ", msg_s});
        return THROW;
    endfunction

endclass

class caliptra_ss_usb_fs_dev_unsupported_ep_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_fs_dev_unsupported_ep_sequence)

    function new(string name = "caliptra_ss_usb_fs_dev_unsupported_ep_sequence");
        super.new(name);
    endfunction

    // Build the 8-byte probe payload. Pattern is incidental; nothing data
    // checks it. Kept non-trivial so it is easy to spot in a waveform.
    protected function void build_probe_payload(ref bit [7:0] data[]);
        data = new[`USB_FS_UNSUPPORTED_EP_BYTES];
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

        caliptra_ss_usb_handshake_counter_callback         pkt_cb;
        caliptra_ss_usb_fs_unsupported_ep_timeout_catcher  to_catcher;

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: wait for the FS link to come up (no chirp handshake at FS;
        // the VIP host is configured high_speed_capable = 0 by the test).
        wait_for_link_enabled(shared_status, "FS host link");

        // Step 2: SOF generation, then let the firmware re-arm EP0 post-reset.
        // The settle delay is stretched relative to HS because one FS frame is
        // 1 ms and the EP0 traffic that follows is 40x slower on the wire.
        start_sof_generation();
        #100us;

        // Step 3: install the handshake counter on the host link monitor. The
        // window is left disarmed so enumeration handshakes are not counted.
        pkt_cb = caliptra_ss_usb_handshake_counter_callback::type_id::create("pkt_cb");
        uvm_callbacks#(svt_usb_link_monitor, svt_usb_link_monitor_callback)::add(
            host_agent_h.link_mon, pkt_cb);
        caliptra_ss_usb_handshake_counter_callback::disarm_window();

        // Step 4: enumerate the hub at address 1, bring up downstream port 1,
        // then enumerate USBDC0 at address 2 (base-class steps A -> B -> C).
        enumerate_hub_and_usbdc0(host_agent_h, usb_cfg);
        `uvm_info("USB_FS_UNSUPPORTED_EP_SEQ", "FS enumeration complete.", UVM_LOW)
        #50us;

        build_probe_payload(probe_data);

        // ---------------------------------------------------------------------
        // The probe: one BULK OUT to an endpoint number with no physical
        // endpoint behind it. The bus must stay silent.
        // ---------------------------------------------------------------------
        `uvm_info("USB_FS_UNSUPPORTED_EP_SEQ",
                  $sformatf("BULK OUT to UNSUPPORTED EP%0d - NO response is expected.",
                            `USB_FS_UNSUPPORTED_EP_NUM),
                  UVM_LOW)

        // Register and arm the timeout catcher only now. Everything before
        // this point (link bring-up, hub and device enumeration) must still be
        // able to fail the run on a timeout, so the catcher is deliberately
        // not installed any earlier.
        to_catcher = new("fs_unsupported_ep_timeout_catcher");
        caliptra_ss_usb_fs_unsupported_ep_timeout_catcher::armed = 1;
        uvm_report_cb::add(null, to_catcher);

        // Declare the stimulus that must be observed on the wire. The counting
        // window stays CLOSED here: the callback opens it at the instant the
        // matching OUT token is actually on the bus, so the silence window can
        // never race the transfer submission.
        caliptra_ss_usb_handshake_counter_callback::expect_probe(
            `USB_FS_UNSUPPORTED_EP_DEV_ADDR,
            `USB_FS_UNSUPPORTED_EP_NUM);

        xfer_returned = 0;
        fork
            begin
                do_data_xfer(
                    .agent_h            (host_agent_h),
                    .usb_cfg            (usb_cfg),
                    .xfer_kind          (svt_usb_transfer::BULK_OUT_TRANSFER),
                    .device_addr        (`USB_FS_UNSUPPORTED_EP_DEV_ADDR),
                    .ep_num             (`USB_FS_UNSUPPORTED_EP_NUM),
                    .byte_count         (`USB_FS_UNSUPPORTED_EP_BYTES),
                    .ep_anchor_idx      (1),
                    .label              ("FS_UNSUPPORTED_EP_OUT"),
                    .req                (probe_req),
                    .obj_name           ("unsupported_ep_probe_req"),
                    // NOTE: do not set no_zero_length_end here. On FS the bulk
                    // max_packet_size is 64 bytes, so an 8-byte OUT is a short
                    // packet and the VIP forces
                    // aligned_transfer_ends_with_zero_length == 1; asking for
                    // 0 makes the transfer constraints unsatisfiable. A short
                    // packet already terminates the transfer.
                    .payload_data       (probe_data));
                xfer_returned = 1;
            end
        join_none

        // Phase 1: wait until the probe is PROVEN to be on the wire. The
        // transfer is submitted in the background above and, by design, never
        // completes (do_data_xfer waits for a transfer-ended notification that
        // only the VIP device_timeout can produce here), so submission alone
        // must never be mistaken for stimulus. Only the link monitor can tell
        // us the OUT token and its DATA packet really left the host.
        fork
            begin
                // Polled, not wait(): the observation flag lives inside the
                // callback class, so a wait() expression built from an
                // accessor function would have no sensitivity to it. One FS
                // frame of granularity is far finer than the windows involved
                // here.
                while (!caliptra_ss_usb_handshake_counter_callback::probe_data_observed())
                    #1us;
            end
            begin
                #(`USB_FS_UNSUPPORTED_EP_STIMULUS_TIMEOUT_US * 1us);
            end
        join_any
        // "disable fork" is a statement, so it needs its own semicolon.
        // Without it the parser folds the next statement into this one and
        // reports a syntax error on the following line.
        disable fork;

        if (!caliptra_ss_usb_handshake_counter_callback::probe_data_observed()) begin
            // Missing stimulus. Reporting bus silence here would be a false
            // pass: nothing was ever sent to EP15, so there was nothing for
            // the device to stay silent about. The silence verdict below is
            // deliberately skipped.
            `uvm_error("USB_FS_UNSUPPORTED_EP_NO_STIMULUS",
                $sformatf("The OUT token / DATA packet for Dev:%0d EP:%0d was never observed on the bus within %0d us, so the probe never reached the wire and no silence measurement is possible (token_seen=%0d, xfer_returned=%0d).",
                          `USB_FS_UNSUPPORTED_EP_DEV_ADDR,
                          `USB_FS_UNSUPPORTED_EP_NUM,
                          `USB_FS_UNSUPPORTED_EP_STIMULUS_TIMEOUT_US,
                          caliptra_ss_usb_handshake_counter_callback::probe_token_observed(),
                          xfer_returned))
        end
        else begin
            `uvm_info("USB_FS_UNSUPPORTED_EP_SEQ",
                $sformatf("Probe observed on the bus: OUT token + %0d-byte DATA packet to Dev:%0d EP:%0d, DATA ended at %0t. Measuring %0d us of bus silence from here.",
                          caliptra_ss_usb_handshake_counter_callback::get_probe_data_bytes(),
                          `USB_FS_UNSUPPORTED_EP_DEV_ADDR,
                          `USB_FS_UNSUPPORTED_EP_NUM,
                          caliptra_ss_usb_handshake_counter_callback::get_probe_data_end_time(),
                          `USB_FS_UNSUPPORTED_EP_SILENCE_US),
                UVM_LOW)

            if (caliptra_ss_usb_handshake_counter_callback::get_probe_data_bytes() !=
                `USB_FS_UNSUPPORTED_EP_BYTES)
                `uvm_error("USB_FS_UNSUPPORTED_EP_SEQ",
                    $sformatf("The observed probe DATA packet carries %0d bytes, expected %0d. The stimulus is not the one this test measures.",
                              caliptra_ss_usb_handshake_counter_callback::get_probe_data_bytes(),
                              `USB_FS_UNSUPPORTED_EP_BYTES))

            // Phase 2: the bounded silence window, measured FROM the observed
            // stimulus and not from the submission. The counting window was
            // opened by the callback when the token appeared, so no device
            // response in between could have been missed.
            #(`USB_FS_UNSUPPORTED_EP_SILENCE_US * 1us);

            caliptra_ss_usb_handshake_counter_callback::disarm_window();

            hs_count = caliptra_ss_usb_handshake_counter_callback::get_handshake_count();
            `uvm_info("USB_FS_UNSUPPORTED_EP_SEQ",
                      $sformatf("Handshakes from device: %0d (ACK=%0d NAK=%0d STALL=%0d), xfer_returned=%0d",
                                hs_count,
                                caliptra_ss_usb_handshake_counter_callback::get_ack_count(),
                                caliptra_ss_usb_handshake_counter_callback::get_nak_count(),
                                caliptra_ss_usb_handshake_counter_callback::get_stall_count(),
                                xfer_returned),
                      UVM_LOW)

            if (hs_count != 0)
                `uvm_error("USB_FS_UNSUPPORTED_EP_SEQ",
                    $sformatf("The UNSUPPORTED endpoint EP%0d responded. %0d handshake(s) observed (ACK=%0d NAK=%0d STALL=%0d); the expected behavior is no response at all.",
                              `USB_FS_UNSUPPORTED_EP_NUM,
                              hs_count,
                              caliptra_ss_usb_handshake_counter_callback::get_ack_count(),
                              caliptra_ss_usb_handshake_counter_callback::get_nak_count(),
                              caliptra_ss_usb_handshake_counter_callback::get_stall_count()))
            else
                `uvm_info("USB_FS_UNSUPPORTED_EP_SEQ",
                    $sformatf("PASSED: the OUT token and its %0d-byte DATA packet to UNSUPPORTED EP%0d were observed on the bus at %0t, and the bus then stayed silent for %0d us.",
                              caliptra_ss_usb_handshake_counter_callback::get_probe_data_bytes(),
                              `USB_FS_UNSUPPORTED_EP_NUM,
                              caliptra_ss_usb_handshake_counter_callback::get_probe_data_end_time(),
                              `USB_FS_UNSUPPORTED_EP_SILENCE_US),
                    UVM_LOW)
        end

        caliptra_ss_usb_handshake_counter_callback::clear_probe_expectation();
        caliptra_ss_usb_handshake_counter_callback::disarm_window();

        // Drain. The catcher stays armed across this delay so the VIP's late
        // device_timeout for the aborted probe transfer cannot fail the run.
        #200us;

        // The probe has drained: remove the catcher so that every later report
        // (in particular the base test's MCU-halt watchdog error) is seen at
        // its original severity.
        caliptra_ss_usb_fs_unsupported_ep_timeout_catcher::armed = 0;
        uvm_report_cb::delete(null, to_catcher);

        `uvm_info("USB_FS_UNSUPPORTED_EP_SEQ",
                  "FS unsupported-endpoint sequence complete.", UVM_LOW)
    endtask

endclass

`undef USB_FS_UNSUPPORTED_EP_BYTES
`undef USB_FS_UNSUPPORTED_EP_SILENCE_US
`undef USB_FS_UNSUPPORTED_EP_STIMULUS_TIMEOUT_US
`undef USB_FS_UNSUPPORTED_EP_NUM
`undef USB_FS_UNSUPPORTED_EP_DEV_ADDR

`endif // CALIPTRA_SS_USB_FS_DEV_UNSUPPORTED_EP_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
