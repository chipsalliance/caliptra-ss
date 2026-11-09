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

`ifndef CALIPTRA_SS_USB_HS_HUB_INT_EP_STATUS_CHANGE_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_HUB_INT_EP_STATUS_CHANGE_SEQUENCE_SV

// =============================================================================
// Hub status-change interrupt endpoint (EP1 IN) polling sequence.
//
// WHAT THIS TEST IS FOR
//
// This is the stimulus for coverage gap G1 of docs/usb_coverage_gaps.md: the
// hub status-change interrupt endpoint is never polled by any existing test,
// which leaves USB_APP_HW_HUB at 12.6% toggle with HUB_EPIN_REQ / HUB_EPIN_GNT
// / HUB_EPIN_RDATA / HUB_EPIN_STALL at 0%, and leaves physical endpoint slot
// [0] of USB_EP_CONFIG_HANDLER (REG_EP_ACTIVE[0], NBYTES_UPDATE_TOGGLE*,
// EP_SET_ENABLE_TOGGLE*) without a single 0->1 transition.
//
// Every other hub test in the repo drives EP0 control transfers only. This one
// drives real INTERRUPT IN tokens at the hub, which is the only way to exercise
// the EP1 IN data path.
//
// THE RTL BEING EXERCISED (all MEASURED from
// third_party/usb2/src/usb_hub_composite_device/RTL/RTL/usb_app_hw_hub.m.vhdl,
// C_HUB_NB_PORTS = 2 and C_DATAWIDTH = 64 in this integration)
//
//   GEN_HUB_STATUS_EP1 (lines 414-421)
//     hub_port_status_change(i) = l1_change(i) or reset_change(i) or
//                                 suspend_change(i) or connect_change(i)
//   PROC_EPIN_ACTIVE (lines 425-433)
//     hub_epin_enable_buffer = hub_dev_status_change or any port_status_change
//     This is what arms the endpoint. With no change pending the endpoint is
//     inactive and the hub NAKs the IN token.
//   hub_epin_gnt <= hub_epin_req (line 439) and PROC_HUB_EPIN_DATA (441-459)
//     hub_epin_rdata_buffer(0)   = hub_dev_status_change (hardwired 0, line 423)
//     hub_epin_rdata_buffer(1)   = port 1 status change
//     hub_epin_rdata_buffer(2)   = port 2 status change
//   hub_epin_buffer_size = ((C_HUB_NB_PORTS+1)/8)+1 = 1 (line 437)
//     So the status-change bitmap this hub returns is exactly ONE byte, and the
//     port under test (port 1) appears in bit 1 of it.
//
// HOW EACH CHANGE BIT IS PRODUCED, AND WHY THE ORDER OF THE STEPS MATTERS
//
// Lines 328-342 force suspend_change, reset_change and l1_change back to 0 on
// EVERY clock unless the port is both connected AND enabled:
//
//   if hub_port_connect(i) = '0'        -> clear suspend/l1/reset change
//   elsif hub_port_enable_int(i) = '0'  -> clear suspend/l1/reset change
//
// so a suspend_change or reset_change leg is only observable AFTER the port has
// been enabled, which on this IP happens through SetPortFeature(PORT_RESET)
// (lines 280-282 set hub_port_reset_int and hub_port_enable_int together).
// Driving ClearPortFeature(PORT_SUSPEND) on a disabled port would latch
// suspend_change for less than a clock and the poll would see nothing - the
// test would then look like an RTL bug when it is a stimulus ordering mistake.
//
// connect_change is the exception. It is set on ANY edge of hub_port_connect
// (lines 202-203) and is NOT in the force-clear list, so it survives
// connect = 0. It is already set when the host first reaches the hub, because
// the firmware asserts USBDC0 DEVCMDSTAT.DCON during boot_usb_core_hub() and
//
//   hub_port_connect(0) <= dev0_usbreg_dev_connect
//
// (ip_xxx_3511_hs_mem_compound_structure.a.vhdl line 2357). That free edge is
// why step 3 below can check the connect_change bitmap without any firmware
// co-operation and without a hotplug FSM.
//
// FLOW
//
//   1. Wait for link ENABLED, start SOF, settle.
//   2. hub_enum_stepA: hub only, at address 1. Downstream ports are NOT brought
//      up - this test talks to the hub and to nothing behind it.
//   3. connect_change leg. GetPortStatus(port 1) must report C_PORT_CONNECTION,
//      then an INTERRUPT IN on EP1 must return a one-byte bitmap with bit 1 set.
//   4. Acknowledge it with ClearPortFeature(C_PORT_CONNECTION) on both ports and
//      confirm wPortChange is clear.
//   5. reset_change leg. SetPortFeature(PORT_RESET) on port 1, confirm bit 20 in
//      the port status word, then poll EP1 IN and require bit 1 again.
//      ClearPortFeature(C_PORT_RESET) afterwards.
//   6. suspend_change leg. SetPortFeature(PORT_SUSPEND) then
//      ClearPortFeature(PORT_SUSPEND) on the now-enabled port 1 - the RTL sets
//      the change bit on the CLEAR, not on the SET (line 233) - confirm bit 18,
//      then poll EP1 IN and require bit 1. ClearPortFeature(C_PORT_SUSPEND)
//      afterwards.
//   7. Idle leg, last. With every change bit acknowledged, poll EP1 IN TWICE
//      in a row with nothing cleared in between. The FIRST poll is
//      informational - it may legitimately drain a buffer that was already
//      armed when the change bits were cleared - and the SECOND poll carries
//      the verdict: it must return no data. Judged from the payload byte count.
//      See poll_int_ep_expect_nak() for why one poll is not sufficient.
//
// WHY THE IDLE LEG IS LAST, AND HOW IT IS BOUNDED
//
// A NAKed interrupt IN only terminates when the host gives up, so it costs
// max_retry_due_to_nak tokens, and the idle leg now issues two such polls. The
// shared configuration raises that budget to 500 for software-polled device
// endpoints, which here would be 500 wasted tokens per poll and a long run. The
// test class therefore lowers the budget on THIS endpoint only (see
// caliptra_ss_usb_hs_hub_int_ep_status_change_test.svh); the hub needs no
// firmware help to answer an IN token so the large budget buys nothing on this
// endpoint.
//
// It is placed last so that, if the VIP ends up complaining at transfer level
// about the deliberately-NAKed transfer, that noise cannot mask the three
// bitmap legs, which are the legs that actually close G1. CHECK_NAK_LEG can be
// set to 0 to drop it without touching anything else.
//
// PORT_RESET SIDE EFFECT (deliberate, and harmless here)
//
// Step 5 bus-resets whatever sits behind port 1, i.e. USBDC0, returning it to
// address 0. This sequence never addresses USBDC0, so nothing downstream of
// that reset is relied upon. The firmware services the resulting DRES_C in its
// normal event loop.
//
// REUSED GOTCHA (claude_md/22_usb_hub_endpoint_halt.md section 7)
//
// do_data_xfer() already waits for completion internally when fork_wait is left
// at its default of 1. wait_xfer_done() is therefore NEVER called after
// do_data_xfer() below: the first wait consumes NOTIFY_USB_TRANSFER_ENDED and a
// second one would block forever. That exact mistake hung the first attempt at
// an interrupt IN probe on this endpoint.
// =============================================================================

class caliptra_ss_usb_hs_hub_int_ep_status_change_sequence
    extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_hub_int_ep_status_change_sequence)

    string MSG_ID = "USB_HUB_INT_EP_SC";

    // USB device address hub_enum_stepA leaves the hub at.
    localparam int HUB_ADDR = 1;

    // Downstream port under test. wIndex is 1-based on the wire; the RTL forms
    // var_port := wIndex - 1, so wIndex 1 is USBDC0 on hub_port_*(0).
    localparam int unsigned PORT_UT = 1;

    // The hub has two downstream ports, so the status-change bitmap is one byte
    // laid out as { 0, 0, 0, 0, 0, port2, port1, hub } - see PROC_HUB_EPIN_DATA.
    localparam int unsigned BITMAP_BYTES    = 1;
    localparam int unsigned BITMAP_BIT_PORT1 = 1;

    // Hub interrupt endpoint. usb_ep_config_hub_pkg.p.vhdl gives device 0 (the
    // hub) exactly one non-control endpoint: EPNB=1, EPDIR=EP_IN, NON_ISO.
    localparam int INT_EP = 1;

    // remote_device_cfg[0].endpoint_cfg[] index of that endpoint, as set up by
    // the test class. Index 1 is the INTERRUPT IN entry.
    localparam int INT_EP_ANCHOR_IDX = 1;

    // Hub class request codes and feature selectors (USB 2.0 table 11-17).
    localparam bit [7:0]  BREQ_GET_STATUS    = 8'h00;
    localparam bit [7:0]  BREQ_CLEAR_FEATURE = 8'h01;
    localparam bit [7:0]  BREQ_SET_FEATURE   = 8'h03;
    localparam bit [15:0] FEAT_PORT_RESET       = 16'h0004;
    localparam bit [15:0] FEAT_PORT_SUSPEND     = 16'h0002;
    localparam bit [15:0] FEAT_C_PORT_CONNECTION = 16'h0010; // 16
    localparam bit [15:0] FEAT_C_PORT_SUSPEND   = 16'h0012;  // 18
    localparam bit [15:0] FEAT_C_PORT_RESET     = 16'h0014;  // 20

    // GetPortStatus returns 4 bytes: wPortStatus then wPortChange, both LE.
    localparam bit [15:0] PORT_STATUS_LEN = 16'h0004;

    // Port status word bit positions (GEN_HUB_PORT_STATUS).
    localparam int unsigned BIT_C_PORT_CONNECTION = 16;
    localparam int unsigned BIT_C_PORT_SUSPEND    = 18;
    localparam int unsigned BIT_C_PORT_RESET      = 20;

    // Settling delay after link-up, before any hub traffic. The VIP link SM
    // walks TRANSMIT -> ENABLED over the first microseconds after bus reset.
    localparam realtime LINK_SETTLE_DELAY = 20us;

    // Let a port status flop settle before the confirming GetPortStatus or the
    // EP1 IN poll. Only has to cover the hub's own EP0 turnaround.
    localparam realtime STATUS_SETTLE = 10us;

    // Set to 0 to drop the final NAK leg (step 7) if its deliberately-aborted
    // transfer ever turns into regression noise. The three bitmap legs are
    // independent of it.
    localparam bit CHECK_NAK_LEG = 1;

    // Transfer timeout for the three POSITIVE EP1 IN legs.
    //
    // do_data_xfer() defaults to 10 ms, which is unusable here: a leg that
    // does not complete then burns 10 ms of simulation before saying so, and
    // there are three of them. Nothing about a working poll is slow - the hub
    // answers an IN token from combinational logic, and every control transfer
    // in this sequence completes in 2-3 us - so a poll that has not completed
    // in 200 us is not slow, it is broken, and the run should say so and move
    // on rather than hang.
    localparam int unsigned INT_LEG_TIMEOUT_US = 200;

    // Shorter still for the NAK leg: nothing is expected to come back, so this
    // only has to cover the (test-reduced) NAK retry budget being exhausted.
    localparam int unsigned NAK_LEG_TIMEOUT_US = 300;

    // Opcode and ack timeout for the MCU STOP handshake at the end of body().
    // The opcode must match MCU_COMMAND_STOP in
    // caliptra_ss_usb_legacy_ep0_observer_if and USB_LEGACY_EP0_COMMAND_STOP
    // in libs/usb/usb.h - all three are the same number and must be changed
    // together.
    localparam bit [3:0] MCU_STOP_OPCODE  = 4'h7;
    localparam realtime  MCU_STOP_ACK_MAX = 200us;

    function new(string name = "caliptra_ss_usb_hs_hub_int_ep_status_change_sequence");
        super.new(name);
    endfunction

    // Step banner. This sequence interleaves hub-class control transfers with
    // EP1 IN data polls and the base-sequence/VIP messages in between are
    // voluminous, so without an explicit marker it is genuinely hard to tell
    // from a log which step is in progress - or, when something hangs, which
    // step it hung in. One line per step, always printed.
    function void step(int num, string what);
        `uvm_info(MSG_ID,
            $sformatf("=== STEP %0d: %s ===", num, what), UVM_LOW)
    endfunction

    // -------------------------------------------------------------------------
    // Main body
    // -------------------------------------------------------------------------
    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: link first, then SOF, then settle.
        step(1, "wait for link ENABLED, start SOF, settle");
        wait_for_link_enabled(shared_status, "HS host link");
        if (link_wait_timed_out) begin
            `uvm_error(MSG_ID,
                "Link never reached ENABLED; aborting hub interrupt endpoint status-change sequence.")
            return;
        end
        start_sof_generation();
        #LINK_SETTLE_DELAY;

        // Step 2: enumerate the hub alone at address 1. hub_enum_stepA leaves
        // the VIP anchor at address 1, so the hub-class requests below need no
        // re-anchoring.
        step(2, $sformatf("enumerate the hub alone at address %0d", HUB_ADDR));
        hub_enum_stepA(host_agent_h, usb_cfg);

        // Push the endpoint model into the host agent before any DATA traffic.
        //
        // The host agent caches the endpoint model it built at build_phase;
        // editing the configuration object alone does not update it. Every
        // working interrupt-endpoint test in the repo does this - see
        // caliptra_ss_usb_hs_dev_int_loopback_sequence, which records that
        // without it "the host issues the new EP token but the modeled device
        // never ACKs it, and the transfer retries to timeout".
        //
        // This test needs it because the test class RETARGETS
        // endpoint_cfg[1] from the shared BULK IN to the hub's INTERRUPT IN,
        // and it does so in build_phase. host_cfg.remote_device_cfg is aliased
        // to dev_cfg.local_device_cfg in the shared configuration, so the edit
        // is visible in this object, but whether the agent has picked it up
        // depends on construction order, which is not something to leave to
        // chance ahead of the only data transfers in the test.
        //
        // The address is NOT what is being refreshed here - every transfer in
        // this sequence targets HUB_ADDR, and hub_enum_stepA already did its
        // own device_address retarget plus reconfigure() above. This call is
        // about the endpoint type/size/direction.
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info(MSG_ID,
            $sformatf({"Pushed endpoint model to the host agent: anchor idx %0d = ",
                       "EP%0d INTERRUPT IN. Each poll requests %0d byte(s), which the ",
                       "host sees as a short packet and so terminates the transfer."},
                      INT_EP_ANCHOR_IDX, INT_EP, BITMAP_BYTES), UVM_LOW)

        // Step 3: connect_change leg. The DCON edge the firmware produced during
        // boot is still outstanding here, so this must be read BEFORE anything
        // acknowledges it.
        step(3, $sformatf({"connect_change leg - GetPortStatus(port %0d) must show ",
                           "C_PORT_CONNECTION, then EP1 IN must return bitmap bit %0d"},
                          PORT_UT, BITMAP_BIT_PORT1));
        get_port_status(host_agent_h, usb_cfg, "connectChange");
        check_port_status_bit("connectChange", BIT_C_PORT_CONNECTION, 1'b1,
                              "C_PORT_CONNECTION");
        poll_int_ep_expect_port_change(host_agent_h, usb_cfg, "connectChange");

        // Step 4: acknowledge the change on BOTH ports. Port 2 is cleared as
        // well so the NAK leg later cannot be defeated by a stale port-2 bit
        // that this test never set but also never cleared.
        step(4, "acknowledge C_PORT_CONNECTION on both ports and confirm it clears");
        clear_port_feature(host_agent_h, usb_cfg, FEAT_C_PORT_CONNECTION, PORT_UT,
                           "C_PORT_CONNECTION_port1");
        clear_port_feature(host_agent_h, usb_cfg, FEAT_C_PORT_CONNECTION, 2,
                           "C_PORT_CONNECTION_port2");
        #STATUS_SETTLE;
        get_port_status(host_agent_h, usb_cfg, "postConnectAck");
        check_port_status_bit("postConnectAck", BIT_C_PORT_CONNECTION, 1'b0,
                              "C_PORT_CONNECTION");

        // Step 5: reset_change leg. SetPortFeature(PORT_RESET) raises
        // hub_port_reset_int and hub_port_enable_int in the same cycle, which is
        // the only condition under which reset_change can latch (lines 205-206).
        // It also leaves the port ENABLED, which the suspend leg below depends
        // on.
        step(5, $sformatf({"reset_change leg - SetPortFeature(PORT_RESET) on port %0d ",
                           "(also ENABLES the port, which step 6 depends on; bus-resets USBDC0)"},
                          PORT_UT));
        set_port_feature(host_agent_h, usb_cfg, FEAT_PORT_RESET, PORT_UT,
                         "PORT_RESET_port1");
        #STATUS_SETTLE;
        get_port_status(host_agent_h, usb_cfg, "resetChange");
        check_port_status_bit("resetChange", BIT_C_PORT_RESET, 1'b1, "C_PORT_RESET");
        poll_int_ep_expect_port_change(host_agent_h, usb_cfg, "resetChange");

        clear_port_feature(host_agent_h, usb_cfg, FEAT_C_PORT_RESET, PORT_UT,
                           "C_PORT_RESET_port1");
        #STATUS_SETTLE;
        get_port_status(host_agent_h, usb_cfg, "postResetAck");
        check_port_status_bit("postResetAck", BIT_C_PORT_RESET, 1'b0, "C_PORT_RESET");

        // Step 6: suspend_change leg. The RTL sets the change bit on the CLEAR
        // of PORT_SUSPEND (line 233), not on the SET, so both requests are
        // needed and only the second one produces the status change.
        step(6, $sformatf({"suspend_change leg - Set then CLEAR PORT_SUSPEND on port %0d ",
                           "(the RTL sets the change bit on the clear, not the set)"},
                          PORT_UT));
        set_port_feature(host_agent_h, usb_cfg, FEAT_PORT_SUSPEND, PORT_UT,
                         "PORT_SUSPEND_port1");
        #STATUS_SETTLE;
        clear_port_feature(host_agent_h, usb_cfg, FEAT_PORT_SUSPEND, PORT_UT,
                           "PORT_SUSPEND_clear_port1");
        #STATUS_SETTLE;
        get_port_status(host_agent_h, usb_cfg, "suspendChange");
        check_port_status_bit("suspendChange", BIT_C_PORT_SUSPEND, 1'b1,
                              "C_PORT_SUSPEND");
        poll_int_ep_expect_port_change(host_agent_h, usb_cfg, "suspendChange");

        clear_port_feature(host_agent_h, usb_cfg, FEAT_C_PORT_SUSPEND, PORT_UT,
                           "C_PORT_SUSPEND_port1");
        #STATUS_SETTLE;
        get_port_status(host_agent_h, usb_cfg, "postSuspendAck");
        check_port_status_bit("postSuspendAck", BIT_C_PORT_SUSPEND, 1'b0,
                              "C_PORT_SUSPEND");

        // Step 7: idle leg. Nothing is outstanding now, so
        // hub_epin_enable_buffer must be 0. Two consecutive polls: the second
        // one must return no data. See poll_int_ep_expect_nak().
        if (CHECK_NAK_LEG) begin
            step(7, "idle leg - two consecutive EP1 IN polls, the SECOND must return NO data");
            poll_int_ep_expect_nak(host_agent_h, usb_cfg, "idle");
        end
        else begin
            step(7, "idle leg SKIPPED (CHECK_NAK_LEG = 0)");
        end

        // Step 8: release the MCU. The firmware has no completion condition of
        // its own in this test - the host addresses only the hub - so it polls
        // until told to stop. Until this handshake existed the firmware halted
        // on a poll budget, which ended the simulation mid-sequence and turned
        // the first EP1 IN wait into a false timeout.
        step(8, "release the MCU with the STOP handshake so it may halt");
        request_mcu_stop();

        `uvm_info(MSG_ID,
            "Hub interrupt endpoint status-change sequence complete.", UVM_LOW)
    endtask

    // -------------------------------------------------------------------------
    // Tell the MCU firmware it may halt, and wait for its ack.
    //
    // Reuses the existing MCI generic-wire command channel from the
    // OCP-recovery work, same as caliptra_ss_usb_fs_dev_lpm_l1_dev_wakeup:
    //   host_mcu_command -> GENERIC_INPUT_WIRES_1 -> firmware polls it
    //   firmware acks via GENERIC_OUTPUT_WIRES_1 -> fw_snapshot_header
    // issue_mcu_command_bounded() holds the command asserted until that ack
    // arrives, so polling firmware cannot miss a pulse.
    //
    // A missing ack is uvm_info, not uvm_error: the firmware has its own
    // bounded fallback and halts without the command, and the base test's
    // MCU-halt monitor still applies. Failing here would make this teardown
    // step able to fail a test whose actual checks all passed.
    // -------------------------------------------------------------------------
    virtual task request_mcu_stop();
        virtual caliptra_ss_usb_legacy_ep0_observer_if observer_vif;
        bit acknowledged;

        if (!uvm_config_db#(
                virtual caliptra_ss_usb_legacy_ep0_observer_if)::get(
                    null, "uvm_test_top.env",
                    "usb_legacy_ep0_observer_if", observer_vif)) begin
            `uvm_info(MSG_ID,
                "No legacy EP0 observer interface in this testbench configuration, so the MCU STOP handshake is skipped. The firmware falls back to its own poll ceiling before halting.",
                UVM_LOW)
            return;
        end

        observer_vif.issue_mcu_command_bounded(
            .opcode(MCU_STOP_OPCODE),
            .generation(16'h0001),
            .expected_legacy_dispatch_delta(4'h0),
            .timeout(MCU_STOP_ACK_MAX),
            .acknowledged(acknowledged));

        if (acknowledged)
            `uvm_info(MSG_ID,
                "MCU STOP acknowledged: the firmware kept USBDC0 serviced for the whole sequence and is now free to halt.",
                UVM_LOW)
        else
            `uvm_info(MSG_ID,
                $sformatf("MCU STOP was not acknowledged within %0t. Not failed here: the firmware halts on its own poll ceiling without the command. If the MCU log also shows no STOP, suspect the firmware was not rebuilt with the STOP check.",
                    MCU_STOP_ACK_MAX),
                UVM_LOW)
    endtask

    // -------------------------------------------------------------------------
    // Poll EP1 IN and require a one-byte status-change bitmap with the bit of
    // the port under test set.
    //
    // This is the load-bearing check of the test: it is the only place where the
    // hub actually has to arm the endpoint, win the DMA grant and return the
    // bitmap. A port status word read over EP0 proves none of that, it only
    // proves the hub latched its own bookkeeping.
    //
    // fork_wait is left at its default, so do_data_xfer() waits internally and
    // wait_xfer_done() must NOT be called here.
    // -------------------------------------------------------------------------
    task poll_int_ep_expect_port_change(svt_usb_agent         host_agent_h,
                                        svt_usb_configuration usb_cfg,
                                        string                tag);
        svt_usb_transfer int_in_req;
        string           label;
        int unsigned     nbytes;
        bit [7:0]        bitmap;
        bit              fail;

        label = {"INT_IN_EP1_", tag};

        // Bracket the blocking call. do_data_xfer() waits internally, so these
        // two lines bound exactly how long the poll took and - if the second
        // one is the last thing in the log - say unambiguously that this is
        // where the sequence stopped, without having to infer it from the
        // absence of later messages.
        `uvm_info(MSG_ID,
            $sformatf({"%s: ENTER EP1 IN poll (addr=%0d ep=%0d want %0d byte(s), ",
                       "anchor idx %0d, timeout %0d us). Expect bitmap bit %0d set."},
                      label, HUB_ADDR, INT_EP, BITMAP_BYTES, INT_EP_ANCHOR_IDX,
                      INT_LEG_TIMEOUT_US, BITMAP_BIT_PORT1), UVM_LOW)

        do_data_xfer(
            .agent_h       (host_agent_h),
            .usb_cfg       (usb_cfg),
            .xfer_kind     (svt_usb_transfer::INTERRUPT_IN_TRANSFER),
            .device_addr   (HUB_ADDR),
            .ep_num        (INT_EP),
            .byte_count    (BITMAP_BYTES),
            .ep_anchor_idx (INT_EP_ANCHOR_IDX),
            .label         (label),
            .req           (int_in_req),
            .obj_name      ({label, "_req"}),
            .timeout_us    (INT_LEG_TIMEOUT_US));

        `uvm_info(MSG_ID,
            $sformatf("%s: EXIT EP1 IN poll, xfer_wait_timed_out=%0b.",
                      label, xfer_wait_timed_out), UVM_LOW)

        // A transfer that ended is not a transfer that succeeded: without this
        // an ABORTED poll would fall through to the payload check and compare
        // against an empty payload.
        check_xfer_status(.xfer             (int_in_req),
                          .label            (label),
                          .min_payload_bytes(BITMAP_BYTES),
                          .fail             (fail));
        if (fail) begin
            `uvm_error(MSG_ID,
                $sformatf({"%s: the hub status-change interrupt endpoint did not ",
                           "return the expected %0d-byte bitmap, so the %s status ",
                           "change was never delivered over EP1 IN. hub_epin_* and ",
                           "the EP1 IN endpoint arming (hub_epin_enable_buffer) are ",
                           "the suspects."},
                          label, BITMAP_BYTES, tag))
            return;
        end

        nbytes = int_in_req.payload_byte_count();
        bitmap = int_in_req.payload.data[0];

        if (bitmap[BITMAP_BIT_PORT1] !== 1'b1) begin
            `uvm_error(MSG_ID,
                $sformatf({"%s: EP1 IN returned bitmap 0x%02h over %0d byte(s), ",
                           "but bit %0d (downstream port %0d) is not set. The hub ",
                           "armed and answered the endpoint yet reported no change ",
                           "for the port whose change bit was just confirmed in the ",
                           "port status word."},
                          label, bitmap, nbytes, BITMAP_BIT_PORT1, PORT_UT))
        end
        else begin
            `uvm_info(MSG_ID,
                $sformatf({"%s: EP1 IN returned bitmap 0x%02h with bit %0d set, so ",
                           "the %s of downstream port %0d was delivered on the hub ",
                           "status-change interrupt endpoint."},
                          label, bitmap, BITMAP_BIT_PORT1, tag, PORT_UT),
                UVM_LOW)
        end
    endtask

    // -------------------------------------------------------------------------
    // Poll EP1 IN TWICE in a row with no change pending, and require that the
    // SECOND poll returns no data.
    //
    // WHY TWO POLLS AND NOT ONE
    //
    // The first version of this leg polled once and failed: with every change
    // bit acknowledged (confirmed by GetPortStatus returning wPortChange =
    // 0x0000) the hub still answered the IN token with one byte of 0x00 instead
    // of NAKing.
    //
    // That single data point does not identify who is wrong, because two
    // different mechanisms predict it equally well:
    //
    //   (a) the endpoint buffer was already armed and loaded at the moment the
    //       host cleared the change bits, so this token legitimately drains one
    //       in-flight buffer. The NEXT token must then NAK.
    //   (b) the endpoint active bit latches and is never cleared, so EVERY
    //       later token is answered. The next token also returns 0x00.
    //
    // Reading (a) is correct hub behaviour and would make the old one-poll
    // check simply wrong. Reading (b) would be an RTL defect. Polling once
    // cannot tell them apart, so the leg now issues two consecutive tokens with
    // nothing cleared in between and takes its verdict from the second:
    //
    //   second poll returns no data -> (a), hub is correct, leg passes
    //   second poll returns data    -> (b), the endpoint is permanently armed
    //
    // The first poll is therefore INFORMATIONAL ONLY and never fails the test -
    // whatever it returns is allowed, and what it returned is logged so the two
    // cases stay distinguishable in the log.
    //
    // check_xfer_status is deliberately NOT used on either poll: a failing
    // transfer status is an expected outcome for a NAKed interrupt IN, so the
    // verdict is taken from the payload byte count, which is the part that is
    // actually wrong if the endpoint is armed when it should not be.
    // -------------------------------------------------------------------------
    task poll_int_ep_expect_nak(svt_usb_agent         host_agent_h,
                                svt_usb_configuration usb_cfg,
                                string                tag);
        svt_usb_transfer int_in_req;
        string           label;
        int unsigned     nbytes;
        int unsigned     first_nbytes;
        bit [7:0]        first_byte;

        for (int unsigned attempt = 1; attempt <= 2; attempt++) begin
            label = $sformatf("INT_IN_EP1_nak_%s_poll%0d", tag, attempt);

            `uvm_info(MSG_ID,
                $sformatf({"%s: polling EP1 IN with every change bit acknowledged ",
                           "(attempt %0d of 2). %s"},
                          label, attempt,
                          (attempt == 1)
                            ? "This first poll is INFORMATIONAL: it may legitimately drain one already-armed buffer, so any payload here is allowed."
                            : "This second poll is the VERDICT: nothing was cleared since the first poll, so the endpoint must now be inactive and return NO data."),
                UVM_LOW)

            do_data_xfer(
                .agent_h       (host_agent_h),
                .usb_cfg       (usb_cfg),
                .xfer_kind     (svt_usb_transfer::INTERRUPT_IN_TRANSFER),
                .device_addr   (HUB_ADDR),
                .ep_num        (INT_EP),
                .byte_count    (BITMAP_BYTES),
                .ep_anchor_idx (INT_EP_ANCHOR_IDX),
                .label         (label),
                .req           (int_in_req),
                .obj_name      ({label, "_req"}),
                .timeout_us    (NAK_LEG_TIMEOUT_US));

            `uvm_info(MSG_ID,
                $sformatf("%s: EXIT EP1 IN poll, xfer_wait_timed_out=%0b.",
                          label, xfer_wait_timed_out), UVM_LOW)

            if (int_in_req == null) begin
                `uvm_error(MSG_ID,
                    $sformatf("%s: no transfer handle returned, so the idle-endpoint check could not be made.",
                              label))
                return;
            end

            nbytes = int_in_req.payload_byte_count();

            if (attempt == 1) begin
                first_nbytes = nbytes;
                first_byte   = (nbytes != 0) ? int_in_req.payload.data[0] : 8'h00;
                if (nbytes != 0)
                    `uvm_info(MSG_ID,
                        $sformatf({"%s: first idle poll returned %0d byte(s), first ",
                                   "byte 0x%02h. Allowed - this is consistent with ",
                                   "draining one buffer that was already armed when ",
                                   "the change bits were cleared. The next poll ",
                                   "decides."},
                                  label, nbytes, first_byte), UVM_LOW)
                else
                    `uvm_info(MSG_ID,
                        $sformatf({"%s: first idle poll already returned no data, so ",
                                   "the endpoint went inactive as soon as the change ",
                                   "bits were cleared."}, label), UVM_LOW)
            end
            else begin
                if (nbytes != 0) begin
                    `uvm_error(MSG_ID,
                        $sformatf({"%s: SECOND consecutive idle poll returned %0d ",
                                   "payload byte(s) (first byte 0x%02h) with no port ",
                                   "or hub status change outstanding and nothing ",
                                   "cleared since the previous poll (which returned ",
                                   "%0d byte(s)). The endpoint is not merely draining ",
                                   "an in-flight buffer - it stays armed, so it must ",
                                   "be the latched endpoint-active bit that is never ",
                                   "cleared rather than a pending change bit."},
                                  label, nbytes, int_in_req.payload.data[0],
                                  first_nbytes))
                end
                else begin
                    `uvm_info(MSG_ID,
                        $sformatf({"%s: second consecutive idle poll returned no ",
                                   "data, as required. The endpoint is inactive once ",
                                   "the already-armed buffer (first poll returned %0d ",
                                   "byte(s)) has been drained."},
                                  label, first_nbytes), UVM_LOW)
                end
            end
        end
    endtask

    // -------------------------------------------------------------------------
    // SetPortFeature on the port under test.
    // -------------------------------------------------------------------------
    task set_port_feature(svt_usb_agent         host_agent_h,
                          svt_usb_configuration usb_cfg,
                          bit [15:0]            feature,
                          int unsigned          port_num,
                          string                tag);
        string label = {"SetPortFeature_", tag};
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::CLASS),
            .bm_request_type_recip(svt_usb_types::BMREQ_OTHER),
            .brequest_val         (BREQ_SET_FEATURE),
            .wvalue               (feature),
            .windex               (16'(port_num)),
            .wlength              (16'h0000),
            .device_addr          (HUB_ADDR),
            .label                (label),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label(label));
    endtask

    // -------------------------------------------------------------------------
    // ClearPortFeature on the given port.
    // -------------------------------------------------------------------------
    task clear_port_feature(svt_usb_agent         host_agent_h,
                            svt_usb_configuration usb_cfg,
                            bit [15:0]            feature,
                            int unsigned          port_num,
                            string                tag);
        string label = {"ClearPortFeature_", tag};
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::CLASS),
            .bm_request_type_recip(svt_usb_types::BMREQ_OTHER),
            .brequest_val         (BREQ_CLEAR_FEATURE),
            .wvalue               (feature),
            .windex               (16'(port_num)),
            .wlength              (16'h0000),
            .device_addr          (HUB_ADDR),
            .label                (label),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label(label));
    endtask

    // -------------------------------------------------------------------------
    // GetPortStatus on the port under test. The response lands in
    // last_ctrl_seq_item, which check_port_status_bit() below reads.
    // -------------------------------------------------------------------------
    task get_port_status(svt_usb_agent         host_agent_h,
                         svt_usb_configuration usb_cfg,
                         string                tag);
        string label = {"GetPortStatus_", tag};
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::CLASS),
            .bm_request_type_recip(svt_usb_types::BMREQ_OTHER),
            .brequest_val         (BREQ_GET_STATUS),
            .wvalue               (16'h0000),
            .windex               (16'(PORT_UT)),
            .wlength              (PORT_STATUS_LEN),
            .device_addr          (HUB_ADDR),
            .label                (label),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label(label));
    endtask

    // -------------------------------------------------------------------------
    // Read one bit out of the last GetPortStatus response and compare it.
    //
    // GetPortStatus returns 4 bytes little-endian: wPortStatus in bytes 0-1 and
    // wPortChange in bytes 2-3. The concatenation below reproduces the RTL
    // hub_status word, so bit numbers 0..31 of GEN_HUB_PORT_STATUS can be used
    // directly.
    //
    // A short or missing payload is an error, not a silent skip: treating it as
    // "nothing to compare" is how a check becomes vacuous.
    // -------------------------------------------------------------------------
    function void check_port_status_bit(string tag, int unsigned bit_idx,
                                        bit exp_val, string bit_name);
        bit [31:0]   status_word;
        int unsigned nbytes;

        if (last_ctrl_seq_item == null) begin
            `uvm_error(MSG_ID,
                $sformatf("%s: no control transfer item captured, so %s could not be checked.",
                          tag, bit_name))
            return;
        end

        nbytes = last_ctrl_seq_item.payload_byte_count();
        if (nbytes < 4) begin
            `uvm_error(MSG_ID,
                $sformatf("%s: GetPortStatus returned %0d payload bytes, expected 4, so %s could not be checked.",
                          tag, nbytes, bit_name))
            return;
        end

        status_word = {last_ctrl_seq_item.payload.data[3],
                       last_ctrl_seq_item.payload.data[2],
                       last_ctrl_seq_item.payload.data[1],
                       last_ctrl_seq_item.payload.data[0]};

        if (status_word[bit_idx] !== exp_val) begin
            `uvm_error(MSG_ID,
                $sformatf("%s: port %0d status bit %0d (%s) is %0b, expected %0b. Full status word 0x%08x.",
                          tag, PORT_UT, bit_idx, bit_name,
                          status_word[bit_idx], exp_val, status_word))
        end
        else begin
            `uvm_info(MSG_ID,
                $sformatf("%s: port %0d status bit %0d (%s) = %0b as expected. Full status word 0x%08x.",
                          tag, PORT_UT, bit_idx, bit_name, exp_val, status_word),
                UVM_LOW)
        end
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_HUB_INT_EP_STATUS_CHANGE_SEQUENCE_SV
