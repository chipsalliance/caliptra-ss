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

`ifndef CALIPTRA_SS_USB_DUAL_DEVICE_HS_DEV0_HOTPLUG_SEQUENCE_SV
`define CALIPTRA_SS_USB_DUAL_DEVICE_HS_DEV0_HOTPLUG_SEQUENCE_SV

// =============================================================================
// USB dual-device High-Speed DEV0 hotplug isolation sequence.
//
// GOAL
//   Prove that connecting / disconnecting USBDC0 (hub downstream port 1) does
//   NOT perturb USBDC1 (hub downstream port 2) while USBDC1 is actively
//   performing EP1 bulk loopback traffic.
//
//   USBDC1 keeps looping 64-byte bulk OUT -> IN transfers for the whole test.
//   USBDC0 is cycled through DEV0_HOTPLUG_CYCLES disconnect / reconnect
//   iterations by the MCU firmware. Any USBDC1 data corruption, NAK storm or
//   transfer timeout observed across a USBDC0 cycle is a port-isolation bug.
//
// WHY THIS WORKS (compound IP structure, ip_xxx_3511_hs_mem_compound_structure)
//   hub_port_connect(0) <= dev0_usbreg_dev_connect;  -- DEV0 DCON = port 1 conn
//   hub_port_connect(1) <= dev1_usbreg_dev_connect;  -- DEV1 DCON = port 2 conn
//   usb_dev_connect <= hub_connect when hub_enable_q = '1'
//                 else dev0_usbreg_dev_connect;
//   hub_connect     <= sync_VBusDebounced and hub_dcon_q;
//
//   Once HUB_EN = 1 the UPSTREAM connect is owned by the hub's own HUB_CONNECT
//   bit, not by DEV0's DCON. Toggling USBDC0.DEVCMDSTAT.DCON therefore produces
//   a DOWNSTREAM port-1 connect/disconnect event only: the upstream link, the
//   hub itself and USBDC1 on port 2 all stay up. No VBUS cycling and no
//   testbench force is needed (contrast caliptra_ss_usb_hs_dev_disconnect,
//   which drives VBUS and tears the whole compound down).
//
//   Port reset isolation comes from the same file:
//     dev0_portreset <= hub_port_reset(0) or sync_busreset
//     dev1_portreset <= hub_port_reset(1) or sync_busreset
//   DEV0's port-1 reset does not reach DEV1. If USBDC1 ever sees its EP entries
//   de-activated or its device address drop back to 0 during a USBDC0 cycle,
//   that is a real isolation failure.
//
// PER-DEVICE REMOTE-DEVICE ANCHORS (important)
//   Every device on the bus has its OWN persistent
//   host_cfg.remote_device_cfg[] slot, created once by the test's build_phase:
//     slot 0 = address 0 (default address, pre-SET_ADDRESS)
//     slot 1 = hub       (address 1)  -> hub_anchor_idx
//     slot 2 = USBDC0    (address 2)  -> usbdc0_anchor_idx
//     slot 3 = USBDC1    (address 3)  -> usbdc1_anchor_idx
//   Each transfer names its target with dev_anchor_idx, so NO slot is ever
//   retargeted and reconfigure() is never called after step 2.
//
//   This replaced a single-slot design that had to retarget slot 0 and call
//   reconfigure() before every transfer. That was the cause of a silent
//   data-toggle bug: reconfigure() rebuilds every endpoint xactor and a fresh
//   BULK endpoint restarts at DATA0, so a device mid-stream desynchronises and
//   USB 2.0 section 8.6 has it discard the next OUT with no completion at all.
//   See the block comment on the anchor fields below for the measured PIDs.
//
//   The USBDC1 bulk traffic and the hub port-1 polling are still INTERLEAVED
//   rather than forked:
//     USBDC1 bulk OUT -> hub port-1 poll -> USBDC1 bulk IN -> hub port-1 poll
//   Separate anchors do remove the old randomize() conflict, but the VIP drives
//   one physical bus through one protocol transactor, and wait_xfer_done()
//   keys off a transactor-wide NOTIFY_USB_TRANSFER_ENDED event that cannot
//   distinguish whose transfer just ended, so concurrent threads would consume
//   each other's completions. Interleaving costs nothing here: the
//   simultaneity that matters is in the DUT - USBDC1's EP1 stays armed in
//   hardware and the hub keeps forwarding to port 2 across the whole window in
//   which port 1 drops and returns. Only the host-side observation is
//   serialized.
//
// FLOW
//   1.  Wait for HS host link ENABLED, start SOF generation, settle.
//   2.  Enumerate the hub (addr 1).
//   3.  Bring up port 1, enumerate USBDC0 at address 2.
//   4.  Bring up port 2, enumerate USBDC1 at address 3.
//   5.  Baseline USBDC1 loopback - proves the steady state before perturbing.
//   6.  For each hotplug cycle:
//        a. Arm a USBDC1 bulk OUT (data now sitting in USBDC1 hardware).
//        b. Poll hub GetPortStatus(port 1) until CURRENT_CONNECT_STATUS = 0,
//           i.e. firmware cleared DEV0 DCON. Error out if it never happens.
//        c. Complete the USBDC1 bulk IN loopback and check the payload. This
//           transfer spans the USBDC0 disconnect - the isolation assertion.
//        d. Poll hub GetPortStatus(port 1) until CURRENT_CONNECT_STATUS = 1
//           again, then re-run port-1 bringup and re-enumerate USBDC0.
//   7.  Final USBDC1 loopback, then a USBDC0 loopback to prove USBDC0 is fully
//       functional again after being hotplugged.
//
// Each USBDC1 iteration uses a distinct payload pattern ((i ^ 8'hFF) + cycle)
// so stale or cross-routed data is caught by the content check rather than
// only by a length check.
//
// Firmware: caliptra_ss_usb_dual_device_hs_dev0_hotplug.c drives the DEV0 DCON
// cycling and keeps re-arming USBDC1's EP1 OUT. The cycle counts here and in
// the firmware must agree (DEV0_HOTPLUG_CYCLES below vs DEV0_TARGET_CYCLES).
// =============================================================================
class caliptra_ss_usb_dual_device_hs_dev0_hotplug_sequence
    extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_dual_device_hs_dev0_hotplug_sequence)

    // USB device addresses assigned to the two controllers. They MUST differ:
    // both controllers share one USB bus behind the hub.
    localparam bit [6:0] USBDC0_ADDR = 7'd2;
    localparam bit [6:0] USBDC1_ADDR = 7'd3;
    localparam bit [6:0] HUB_ADDR    = 7'd1;

    // Number of DEV0 disconnect/reconnect iterations. MUST match
    // DEV0_TARGET_CYCLES in caliptra_ss_usb_dual_device_hs_dev0_hotplug.c.
    localparam int unsigned DEV0_HOTPLUG_CYCLES = 3;

    // Bulk loopback size, matching the firmware's USB_BULK_LOOPBACK_BYTES.
    localparam int unsigned LOOPBACK_BYTES = 64;

    // Hub port-1 status polling budget. Each poll is one GetPortStatus control
    // transfer plus POLL_INTERVAL of bus time, so this must comfortably outlast
    // the firmware's disconnect hold. If the budget is exhausted the expected
    // connect-status edge never arrived and the test fails loudly rather than
    // passing vacuously.
    localparam int unsigned PORT_POLL_MAX_ATTEMPTS = 60;
    localparam time         PORT_POLL_INTERVAL     = 20us;

    // Extra settling time between a hub downstream port reset and the first
    // SETUP addressed to the device behind that port.
    //
    // A hub port reset propagates a USB bus reset into the device controller
    // behind it, and the IP_3511 clears the Active bit on EVERY endpoint entry
    // when it sees one. The device NAKs every token until firmware notices
    // DEVCMDSTAT.DRES_C and runs usb_handle_bus_reset() -> usb_ep0_reinit() to
    // re-arm the EP0 OUT/SETUP entries. USB 2.0 section 8.5.3 forbids NAKing a
    // SETUP, so a SETUP landing inside that re-arm window is reported by the
    // VIP as valid_device_response_check ("Received a NAK device response to a
    // host SETUP packet which is a violation") even though the VIP's retries
    // eventually push the transfer through. This is a firmware-latency effect,
    // not a line-speed effect.
    //
    // hub_port_bringup_stepB() already waits 10 us after the reset, which is
    // enough for the plain HS dual-device loopback test. It is not enough here
    // because this firmware services BOTH controllers from one polling loop AND
    // runs the DEV0 hotplug FSM in the same loop, so one controller's DRES_C
    // handling can be queued behind the other's servicing. 80 us is roughly
    // ten HS microframes of additional margin and keeps the total stimulus
    // length essentially unchanged; the FS variant of this test needs a much
    // larger value only because an FS frame is 1 ms.
    localparam time         POST_PORT_RESET_SETTLE = 80us;

    // Settle time before each USBDC1 EP1 BULK OUT.
    //
    // THIS IS LATENCY TUNING, NOT A CORRECTNESS REQUIREMENT, and no check in
    // this sequence may be allowed to depend on it. An endpoint the firmware
    // has not armed yet NAKs, and the host retries the transaction until
    // device_timeout, so arming late costs microseconds of NAK and nothing
    // else. The log proves it twice over:
    //   740416 ns  DATA HS_BULK_OUT_EP1_dev1_cyc0 issued
    //   744325 ns  MCU: dev1 EP1 OUT armed for 64 bytes
    //   795115 ns  Transfer HS_BULK_OUT_EP1_dev1_cyc0 completed
    // (~55 us of NAK, then success) and, in the round-14 run, an arm 5.5 us
    // after the OUT was issued that also completed normally.
    //
    // What the wait buys is a cleaner experiment: the firmware re-arms EP1 OUT
    // only after it has seen the previous EP1 IN complete, from the same
    // polling loop that services USBDC0 and runs the hotplug FSM, so without a
    // settle the run is longer and the USBDC1-traffic / USBDC0-hotplug overlap
    // this test exists to create is skewed by NAK retries. 20 us matches the
    // OUT -> IN settle below and comfortably exceeds the observed re-arm
    // latency. Removing it should slow the test down, never fail it - if it
    // ever does fail it, the bug is in the firmware's arm path, not here.
    localparam time         PRE_BULK_OUT_SETTLE    = 20us;

    // Settle time between a USBDC1 EP1 BULK OUT completing and the matching
    // EP1 BULK IN being issued.
    //
    // LATENCY TUNING ONLY, for the same reason as PRE_BULK_OUT_SETTLE above.
    // The firmware copies EP1 OUT -> EP1 IN and arms EP1 IN only after polling
    // the EP1 OUT entry and seeing Active clear, which costs a few microseconds
    // of polling latency; an IN issued before that is NAKed and retried.
    //
    // An earlier version of this comment claimed that an IN against an un-armed
    // endpoint "returned an EMPTY payload", and that claim sent several rounds
    // of debug in the wrong direction. It is wrong: the empty payload is read
    // after wait_xfer_done() has exhausted the whole device_timeout retry
    // budget, so it means the endpoint never became ready at all - a permanent
    // stall, typically a data-toggle desync. See check_loopback() for the
    // correct diagnosis. Both the baseline and hotplug-cycle paths use this
    // constant simply so the stimulus does not spend its time NAKing.
    localparam time         POST_BULK_OUT_SETTLE   = 20us;

    // -------------------------------------------------------------------------
    // Persistent remote-device slot indices, one per bus address, published by
    // the test's build_phase (see
    // caliptra_ss_usb_dual_device_hs_dev0_hotplug_test). Every transfer selects
    // its target by passing one of these as dev_anchor_idx, so no slot is ever
    // retargeted and reconfigure() is never called once bring-up is done.
    //
    // THIS IS THE FIX FOR A SILENT DATA-TOGGLE BUG. The previous design kept a
    // single slot and retargeted it before every transfer:
    //
    //     usb_cfg.remote_device_cfg[0].device_address = addr;
    //     host_agent_h.reconfigure(usb_cfg);          // select_remote_device()
    //
    // reconfigure() rebuilds EVERY endpoint protocol processor on the agent,
    // and a freshly built BULK endpoint restarts its DATA TOGGLE at DATA0. Per
    // USB 2.0 section 8.6 a device that expects DATA1 and receives DATA0
    // DISCARDS the packet as a presumed retransmission - and does so silently:
    // no buffer write, no descriptor retire, no completion interrupt. The
    // firmware's completion poll therefore never fires, EP1 IN is never armed,
    // and the paired BULK IN NAKs until its retry budget is exhausted.
    //
    // The measured USBDC1 EP1 BULK OUT PIDs in the failing run were
    // DATA0, DATA1, DATA0, DATA0 - the fourth needed to be DATA1. Each fresh
    // xactor restarts at DATA0, so the first three were correct only by
    // coincidence (OUT 2 reused a surviving instance; OUT 1 and 3 wanted DATA0
    // anyway) and OUT 4 was simply the first transfer at which the reset was
    // observable. That is exactly why three loopbacks passed and the fourth
    // killed the endpoint. The full evidence table is in
    // caliptra_ss_usb_shared_cfg::add_remote_device_slot.
    //
    // CONSEQUENCE FOR MAINTAINERS: do NOT reintroduce a reconfigure() anywhere
    // in this sequence after step 2. It would reset the toggles of ALL devices,
    // including ones this sequence is not touching.
    // -------------------------------------------------------------------------
    int hub_anchor_idx;
    int usbdc0_anchor_idx;
    int usbdc1_anchor_idx;

    // Slot 0 keeps device_address 0 - the default address a device answers on
    // between a hub port reset and SET_ADDRESS - so it serves the
    // default-address stage of every enumeration.
    localparam int ADDR0_ANCHOR_IDX = 0;

    function new(string name = "caliptra_ss_usb_dual_device_hs_dev0_hotplug_sequence");
        super.new(name);
    endfunction

    // Fetch the slot indices the test published. Fatals rather than silently
    // falling back to 0: a missing index would send every transfer through
    // slot 0, which still sits at device_address 0, and the VIP constraint
    // device_address == dev_anchor.device_address would then fail randomize()
    // in a way that is far harder to read than this message.
    function void resolve_device_anchors();
        // Read with (null, "*"), the global scope. The test publishes these
        // with uvm_config_db#(int)::set(null, "*", ...) from its build_phase.
        // Both halves of the pair matter: an earlier version used
        // set(this, "*", ...) in the test, which stores under the scope
        // "uvm_test_top.*" and matches neither "uvm_test_top" nor "*" here, so
        // the get() returned 0 and tripped the uvm_fatal below. This sequence
        // runs on the host agent virtual sequencer, not under the test, so a
        // test-relative scope cannot reach it. Matches the working pattern of
        // usb_int_ep_num in caliptra_ss_usb_hs_dev_int_loopback_sequence.svh.

        if (!uvm_config_db#(int)::get(null, "*", "hub_anchor_idx",
                                      hub_anchor_idx))
            `uvm_fatal("USB_DEV0_HOTPLUG_SEQ",
                "hub_anchor_idx not found in config_db - the test must call add_remote_device_slot() and publish it.")
        if (!uvm_config_db#(int)::get(null, "*", "usbdc0_anchor_idx",
                                      usbdc0_anchor_idx))
            `uvm_fatal("USB_DEV0_HOTPLUG_SEQ",
                "usbdc0_anchor_idx not found in config_db - the test must call add_remote_device_slot() and publish it.")
        if (!uvm_config_db#(int)::get(null, "*", "usbdc1_anchor_idx",
                                      usbdc1_anchor_idx))
            `uvm_fatal("USB_DEV0_HOTPLUG_SEQ",
                "usbdc1_anchor_idx not found in config_db - the test must call add_remote_device_slot() and publish it.")

        `uvm_info("USB_DEV0_HOTPLUG_SEQ",
            $sformatf({"Device anchors resolved: addr0=%0d hub=%0d ",
                       "usbdc0=%0d usbdc1=%0d."},
                      ADDR0_ANCHOR_IDX, hub_anchor_idx,
                      usbdc0_anchor_idx, usbdc1_anchor_idx), UVM_LOW)
    endfunction

    // Issue a single hub GetPortStatus(port_num) and return the reported
    // CURRENT_CONNECT_STATUS bit (wPortStatus bit 0).
    //
    // The 4-byte response is wPortStatus[15:0] followed by wPortChange[15:0],
    // little endian, so payload byte 0 bit 0 is CURRENT_CONNECT_STATUS.
    // The VIP anchor must already be at the hub address (1) on entry.
    task automatic get_port_connect_status(svt_usb_agent host_agent_h,
                                           svt_usb_configuration usb_cfg,
                                           int port_num,
                                           string label,
                                           output bit connected);
        string lbl;
        lbl = $sformatf("GetPortStatus_Port%0d_%s", port_num, label);

        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::CLASS),
            .bm_request_type_recip(svt_usb_types::BMREQ_OTHER),
            .brequest_val         (8'h00),
            .wvalue               (16'h0000),
            .windex               (16'(port_num)),
            .wlength              (16'h0004),
            .device_addr          (int'(HUB_ADDR)),
            .label                (lbl),
            .usb_cfg              (usb_cfg),
            .dev_anchor_idx       (hub_anchor_idx));
        wait_xfer_done(.agent_h(host_agent_h), .label(lbl));

        if (last_ctrl_seq_item == null
            || last_ctrl_seq_item.payload_byte_count() < 1) begin
            `uvm_error("USB_DEV0_HOTPLUG_SEQ",
                $sformatf("%s returned no payload - cannot read port status.",
                          lbl))
            connected = 1'b0;
            return;
        end

        connected = last_ctrl_seq_item.payload.data[0][0];
        `uvm_info("USB_DEV0_HOTPLUG_SEQ",
            $sformatf("%s: wPortStatus[7:0]=0x%02h CURRENT_CONNECT_STATUS=%0b",
                      lbl, last_ctrl_seq_item.payload.data[0], connected),
            UVM_MEDIUM)
    endtask

    // Poll hub port_num until CURRENT_CONNECT_STATUS reaches want_connected.
    // Raises a uvm_error and sets timed_out if the edge never arrives, so a
    // missed hotplug event is a hard failure instead of a silent pass.
    //
    // Every poll is addressed through the hub's own persistent anchor, so no
    // anchor retarget (and therefore no reconfigure()) is needed here. That
    // matters because these polls run while USBDC1 is mid-bulk-stream.
    task automatic wait_port_connect_status(svt_usb_agent host_agent_h,
                                            svt_usb_configuration usb_cfg,
                                            int port_num,
                                            bit want_connected,
                                            string label,
                                            output bit timed_out);
        bit          connected;
        int unsigned attempt;

        timed_out = 1'b0;

        for (attempt = 0; attempt < PORT_POLL_MAX_ATTEMPTS; attempt++) begin
            get_port_connect_status(
                .host_agent_h(host_agent_h),
                .usb_cfg     (usb_cfg),
                .port_num    (port_num),
                .label       ($sformatf("%s_poll%0d", label, attempt)),
                .connected   (connected));

            if (connected === want_connected) begin
                `uvm_info("USB_DEV0_HOTPLUG_SEQ",
                    $sformatf("Hub port %0d reached CONNECT_STATUS=%0b after %0d poll(s) (%s).",
                              port_num, want_connected, attempt + 1, label),
                    UVM_LOW)
                return;
            end
            #PORT_POLL_INTERVAL;
        end

        timed_out = 1'b1;
        `uvm_error("USB_DEV0_HOTPLUG_SEQ",
            $sformatf("Hub port %0d never reached CONNECT_STATUS=%0b within %0d polls (%s). The expected DEV0 hotplug edge was missed - firmware DEV0_DISCONNECT_HOLD_US may be outside the observable window, or DEV0 DCON is not reaching hub_port_connect(0).",
                      port_num, want_connected, PORT_POLL_MAX_ATTEMPTS, label))
    endtask

    // Acknowledge the port connect-status change (ClearFeature
    // C_PORT_CONNECTION, feature selector 0x10) so the next change edge is
    // observable. The VIP anchor must be at the hub address on entry.
    task automatic clear_port_connection_change(svt_usb_agent host_agent_h,
                                                 svt_usb_configuration usb_cfg,
                                                 int port_num,
                                                 string label);
        string lbl;
        lbl = $sformatf("ClearFeature_C_PORT_CONNECTION_Port%0d_%s",
                        port_num, label);

        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::CLASS),
            .bm_request_type_recip(svt_usb_types::BMREQ_OTHER),
            .brequest_val         (8'h01),
            .wvalue               (16'h0010),
            .windex               (16'(port_num)),
            .wlength              (16'h0000),
            .device_addr          (int'(HUB_ADDR)),
            .label                (lbl),
            .usb_cfg              (usb_cfg),
            .dev_anchor_idx       (hub_anchor_idx));
        wait_xfer_done(.agent_h(host_agent_h), .label(lbl));
    endtask

    // Build the per-iteration USBDC1 payload. Distinct per cycle so stale data
    // left over from a previous iteration is caught by the content check.
    function automatic void build_dev1_pattern(int unsigned cycle,
                                               ref bit [7:0] data[]);
        data = new[LOOPBACK_BYTES];
        for (int unsigned i = 0; i < LOOPBACK_BYTES; i++)
            data[i] = (i[7:0] ^ 8'hFF) + cycle[7:0];
    endfunction

    // One complete USBDC1 EP1 bulk OUT -> IN loopback with payload check.
    // ep_anchor_idx 2 = EP1 BULK OUT, 1 = EP1 BULK IN (see the test's
    // endpoint_cfg[] layout). HS EP1 bulk max_packet_size is 512 so a 64-byte
    // OUT is a valid short packet - do NOT set no_zero_length_end.
    task automatic dev1_loopback(svt_usb_agent host_agent_h,
                                  svt_usb_configuration usb_cfg,
                                  string label);
        svt_usb_transfer out_req, in_req;
        bit [7:0]        data[];

        build_dev1_pattern(0, data);

        // Give the firmware time to re-arm EP1 OUT after the previous
        // iteration's EP1 IN completion before issuing the next OUT.
        #PRE_BULK_OUT_SETTLE;

        do_data_xfer(
            .agent_h       (host_agent_h),
            .usb_cfg       (usb_cfg),
            .xfer_kind     (svt_usb_transfer::BULK_OUT_TRANSFER),
            .device_addr   (int'(USBDC1_ADDR)),
            .ep_num        (1),
            .byte_count    (LOOPBACK_BYTES),
            .ep_anchor_idx (2),
            .label         ({"HS_BULK_OUT_EP1_dev1_", label}),
            .req           (out_req),
            .obj_name      ("dev1_out_req"),
            .payload_data  (data),
            .dev_anchor_idx(usbdc1_anchor_idx));

        // Let the MCU copy EP1 OUT -> EP1 IN and arm EP1 IN.
        #POST_BULK_OUT_SETTLE;

        do_data_xfer(
            .agent_h       (host_agent_h),
            .usb_cfg       (usb_cfg),
            .xfer_kind     (svt_usb_transfer::BULK_IN_TRANSFER),
            .device_addr   (int'(USBDC1_ADDR)),
            .ep_num        (1),
            .byte_count    (LOOPBACK_BYTES),
            .ep_anchor_idx (1),
            .label         ({"HS_BULK_IN_EP1_dev1_", label}),
            .req           (in_req),
            .obj_name      ("dev1_in_req"),
            .dev_anchor_idx(usbdc1_anchor_idx));

        check_loopback({"USBDC1_", label}, in_req, data);
    endtask

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;
        svt_usb_transfer      dev0_out_req, dev0_in_req;
        svt_usb_transfer      dev1_out_req, dev1_in_req;
        bit [7:0]             dev0_data[];
        bit [7:0]             dev1_data[];
        bit                   poll_timed_out;
        int unsigned          cycle;
        int unsigned          i;

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();
        resolve_device_anchors();

        // Step 1: Wait for HS link ENABLED, keep it alive, let firmware settle.
        wait_for_link_enabled(shared_status, "HS host link");
        if (link_wait_timed_out) return;
        start_sof_generation();
        #50us;

        // Step 2: Enumerate the hub, addressing it through its own persistent
        // slot.
        //
        // Passing hub_anchor_idx makes hub_enum_stepA SKIP the slot-0
        // retarget and the reconfigure() it would otherwise do after
        // SET_ADDRESS(1). Both halves of that matter here:
        //
        //  - Correctness. The hub slot ALREADY holds address 1, so assigning
        //    address 1 to slot 0 as well would put two remote_device_cfg[]
        //    entries on the same address. reconfigure() validates the whole
        //    configuration and rejects a duplicate outright
        //    ("device_address must be unique within remote_device_cfg"),
        //    which the VIP escalates to a uvm_fatal in
        //    svt_agent::change_dynamic_cfg - it killed the run at 398417 ns.
        //
        //  - The no-reconfigure invariant. With this call anchored, there is
        //    now NO reconfigure() anywhere in this sequence, so nothing can
        //    rebuild a bulk endpoint xactor and reset its data toggle
        //    mid-stream.
        //
        // Slot 0 is left untouched at address 0, which is the role it holds
        // for the whole run: the address a device answers on between a hub
        // port reset and its SET_ADDRESS.
        hub_enum_stepA(
            .host_agent_h  (host_agent_h),
            .usb_cfg       (usb_cfg),
            .dev_anchor_idx(hub_anchor_idx));


        // Step 3: Bring up port 1 and enumerate USBDC0 at address 2.
        hub_port_bringup_stepB(
            .host_agent_h  (host_agent_h), .usb_cfg(usb_cfg), .port_num(1),
            .dev_anchor_idx(hub_anchor_idx));
        // Let firmware observe DRES_C and re-arm EP0 before the first SETUP.
        #POST_PORT_RESET_SETTLE;
        usbdc0_enum_stepC(
            .host_agent_h        (host_agent_h),
            .usb_cfg             (usb_cfg),
            .suffix              ("_dev0_init"),
            .device_idx          (0),
            .assign_address      (USBDC0_ADDR),
            .addr0_anchor_idx    (ADDR0_ANCHOR_IDX),
            .addressed_anchor_idx(usbdc0_anchor_idx));

        // Step 4: Bring up port 2 and enumerate USBDC1 at address 3.
        //
        // No re-anchoring step is needed any more. The hub-class requests below
        // are addressed through hub_anchor_idx and the USBDC0 enumeration above
        // never disturbed it, so the old
        // "select_remote_device(host_agent_h, usb_cfg, HUB_ADDR)" that used to
        // sit here - and the reconfigure() inside it - are gone.
        hub_port_bringup_stepB(
            .host_agent_h  (host_agent_h), .usb_cfg(usb_cfg), .port_num(2),
            .dev_anchor_idx(hub_anchor_idx));
        // Let firmware observe DRES_C and re-arm EP0 before the first SETUP.
        #POST_PORT_RESET_SETTLE;
        usbdc0_enum_stepC(
            .host_agent_h        (host_agent_h),
            .usb_cfg             (usb_cfg),
            .suffix              ("_dev1"),
            .device_idx          (1),
            .assign_address      (USBDC1_ADDR),
            .addr0_anchor_idx    (ADDR0_ANCHOR_IDX),
            .addressed_anchor_idx(usbdc1_anchor_idx));

        `uvm_info("USB_DEV0_HOTPLUG_SEQ",
            "Dual-device enumeration complete (USBDC0@2, USBDC1@3).", UVM_LOW)
        #10us;

        // Step 5: Baseline USBDC1 loopback. Establishes that USBDC1 works
        // before any USBDC0 perturbation, so a later failure is attributable to
        // the hotplug activity rather than to a broken starting state.
        dev1_loopback(host_agent_h, usb_cfg, "baseline");

        // Step 6: Hotplug cycles. The firmware drives DEV0 DCON; this sequence
        // observes the resulting hub port-1 events and keeps USBDC1 busy across
        // each one.
        for (cycle = 0; cycle < DEV0_HOTPLUG_CYCLES; cycle++) begin
            `uvm_info("USB_DEV0_HOTPLUG_SEQ",
                $sformatf("=== DEV0 hotplug cycle %0d/%0d ===",
                          cycle + 1, DEV0_HOTPLUG_CYCLES), UVM_LOW)

            build_dev1_pattern(cycle + 1, dev1_data);

            // 6a. Arm a USBDC1 bulk OUT. After this returns the data is held in
            // USBDC1 hardware and the MCU is about to copy it to EP1 IN, so
            // USBDC1 is genuinely mid-operation for the rest of this cycle.
            //
            // Same pre-OUT settle as in dev1_loopback(): the previous
            // iteration's EP1 IN completion is what makes the firmware re-arm
            // EP1 OUT, and that re-arm must land before this OUT is issued or
            // the OUT just NAKs until it does.
            #PRE_BULK_OUT_SETTLE;
            do_data_xfer(
                .agent_h       (host_agent_h),
                .usb_cfg       (usb_cfg),
                .xfer_kind     (svt_usb_transfer::BULK_OUT_TRANSFER),
                .device_addr   (int'(USBDC1_ADDR)),
                .ep_num        (1),
                .byte_count    (LOOPBACK_BYTES),
                .ep_anchor_idx (2),
                .label         ($sformatf("HS_BULK_OUT_EP1_dev1_cyc%0d", cycle)),
                .req           (dev1_out_req),
                .obj_name      ("dev1_out_req"),
                .payload_data  (dev1_data),
                .dev_anchor_idx(usbdc1_anchor_idx));

            // 6b. Observe USBDC0 dropping off hub port 1.
            wait_port_connect_status(
                .host_agent_h   (host_agent_h),
                .usb_cfg        (usb_cfg),
                .port_num       (1),
                .want_connected (1'b0),
                .label          ($sformatf("disconnect_cyc%0d", cycle)),
                .timed_out      (poll_timed_out));
            if (poll_timed_out) break;
            clear_port_connection_change(
                host_agent_h, usb_cfg, 1,
                $sformatf("disconnect_cyc%0d", cycle));

            // 6c. Complete the USBDC1 loopback. This IN transfer is issued
            // while hub port 1 is DOWN, so a pass here is the direct evidence
            // that USBDC0's disconnect did not disturb USBDC1.
            //
            // The hub port-1 poll and ClearFeature above do NOT reliably cover
            // the firmware's EP1 OUT -> EP1 IN turnaround, so wait explicitly
            // for it here exactly as dev1_loopback() does. Without this the IN
            // hits an un-armed EP1 and returns an empty payload.
            #POST_BULK_OUT_SETTLE;
            do_data_xfer(
                .agent_h       (host_agent_h),
                .usb_cfg       (usb_cfg),
                .xfer_kind     (svt_usb_transfer::BULK_IN_TRANSFER),
                .device_addr   (int'(USBDC1_ADDR)),
                .ep_num        (1),
                .byte_count    (LOOPBACK_BYTES),
                .ep_anchor_idx (1),
                .label         ($sformatf("HS_BULK_IN_EP1_dev1_cyc%0d", cycle)),
                .req           (dev1_in_req),
                .obj_name      ("dev1_in_req"),
                .dev_anchor_idx(usbdc1_anchor_idx));
            check_loopback($sformatf("USBDC1_dev0_down_cyc%0d", cycle),
                           dev1_in_req, dev1_data);

            // 6d. Observe USBDC0 coming back, then re-enumerate it. The
            // firmware re-asserts DCON, which re-raises hub_port_connect(0).
            wait_port_connect_status(
                .host_agent_h   (host_agent_h),
                .usb_cfg        (usb_cfg),
                .port_num       (1),
                .want_connected (1'b1),
                .label          ($sformatf("reconnect_cyc%0d", cycle)),
                .timed_out      (poll_timed_out));
            if (poll_timed_out) break;

            // hub_port_bringup_stepB() does its own GetPortStatus +
            // ClearFeature(C_PORT_CONNECTION) + SetFeature(PORT_RESET) +
            // ClearFeature(C_PORT_RESET), which is exactly the re-attach
            // handling a real host performs. The anchor is already at the hub
            // address after the poll above, as it requires.
            hub_port_bringup_stepB(
                .host_agent_h  (host_agent_h),
                .usb_cfg       (usb_cfg),
                .suffix        ($sformatf("_dev0_recon%0d", cycle)),
                .port_num      (1),
                .dev_anchor_idx(hub_anchor_idx));
            // Let firmware observe DRES_C and re-arm EP0 before the first
            // SETUP of the re-enumeration.
            #POST_PORT_RESET_SETTLE;
            // Re-enumerating USBDC0 through persistent anchors is what makes
            // this cycle safe for USBDC1: the old single-slot form called
            // reconfigure() twice here (once to reach address 0, once after
            // SET_ADDRESS), and each of those rebuilt USBDC1's EP1 BULK
            // endpoint and reset its data toggle while USBDC1 was mid-stream.
            usbdc0_enum_stepC(
                .host_agent_h        (host_agent_h),
                .usb_cfg             (usb_cfg),
                .suffix              ($sformatf("_dev0_recon%0d", cycle)),
                .device_idx          (0),
                .assign_address      (USBDC0_ADDR),
                .addr0_anchor_idx    (ADDR0_ANCHOR_IDX),
                .addressed_anchor_idx(usbdc0_anchor_idx));

            `uvm_info("USB_DEV0_HOTPLUG_SEQ",
                $sformatf("DEV0 hotplug cycle %0d complete: USBDC0 re-enumerated at address %0d, USBDC1 loopback unaffected.",
                          cycle + 1, USBDC0_ADDR), UVM_LOW)
        end

        // Step 7a: USBDC1 must still be healthy after all the hotplug activity.
        dev1_loopback(host_agent_h, usb_cfg, "final");

        // Step 7b: USBDC0 must be fully functional again after its last
        // reconnect - a one-shot EP1 loopback on the freshly re-enumerated
        // controller.
        dev0_data = new[LOOPBACK_BYTES];
        for (i = 0; i < LOOPBACK_BYTES; i++)
            dev0_data[i] = i[7:0];

        do_data_xfer(
            .agent_h       (host_agent_h),
            .usb_cfg       (usb_cfg),
            .xfer_kind     (svt_usb_transfer::BULK_OUT_TRANSFER),
            .device_addr   (int'(USBDC0_ADDR)),
            .ep_num        (1),
            .byte_count    (LOOPBACK_BYTES),
            .ep_anchor_idx (2),
            .label         ("HS_BULK_OUT_EP1_dev0_final"),
            .req           (dev0_out_req),
            .obj_name      ("dev0_out_req"),
            .payload_data  (dev0_data),
            .dev_anchor_idx(usbdc0_anchor_idx));

        #POST_BULK_OUT_SETTLE;

        do_data_xfer(
            .agent_h       (host_agent_h),
            .usb_cfg       (usb_cfg),
            .xfer_kind     (svt_usb_transfer::BULK_IN_TRANSFER),
            .device_addr   (int'(USBDC0_ADDR)),
            .ep_num        (1),
            .byte_count    (LOOPBACK_BYTES),
            .ep_anchor_idx (1),
            .label         ("HS_BULK_IN_EP1_dev0_final"),
            .req           (dev0_in_req),
            .obj_name      ("dev0_in_req"),
            .dev_anchor_idx(usbdc0_anchor_idx));

        check_loopback("USBDC0_post_hotplug", dev0_in_req, dev0_data);

        // Allow the MCU time to log its own completion verdict.
        #20us;

        `uvm_info("USB_DEV0_HOTPLUG_SEQ",
            $sformatf("USB dual-device HS DEV0 hotplug isolation sequence complete (%0d cycles).",
                      DEV0_HOTPLUG_CYCLES), UVM_LOW)
    endtask

    // Compare a received bulk IN payload against the bytes sent to that
    // controller, erroring on any mismatch.
    //
    // The payload length is validated BEFORE the per-byte compare. A BULK IN
    // that is issued against an endpoint the firmware has not re-armed yet is
    // NAKed and comes back with an EMPTY payload, which reads out as all-zero
    // data. Doing the per-byte loop first turns that single handshake race into
    // 63 "mismatch at byte[n]: sent=0xNN received=0x00" errors that look like
    // data corruption and hide the real cause, so the short/empty case is
    // reported once, explicitly, and the per-byte compare is skipped.
    function void check_loopback(string dev_name, svt_usb_transfer in_req,
                                 bit [7:0] sent[]);
        int mismatch_count;
        int unsigned rx_bytes;
        mismatch_count = 0;

        if (in_req == null) begin
            `uvm_error("USB_DEV0_HOTPLUG_SEQ",
                $sformatf("%s loopback check FAILED: no IN transfer object.",
                          dev_name))
            return;
        end

        // A short or empty payload is NOT a race with the firmware's re-arm.
        // This value is read after do_data_xfer() -> wait_xfer_done() has
        // already returned, i.e. after the VIP exhausted its entire retry
        // budget (device_timeout). An endpoint that is merely late to be armed
        // NAKs and the host retries until it succeeds - that costs latency, not
        // payload. Reaching here therefore means the endpoint NEVER became
        // ready, which on this design has two realistic causes:
        //   1. a data-toggle desync, which is silent on the wire: the device
        //      ACKs the mismatched packet and discards it, so Active is never
        //      cleared and the firmware's completion poll never fires again;
        //   2. the firmware lost or never reached the arm (stale state, wedged
        //      service loop, controller detached underneath it).
        // Check the MCU log for the matching "EP1 IN armed" line and for a
        // data_toggle_check_* error from the VIP - do NOT reach for the settle
        // constants, which are latency tuning only.
        rx_bytes = in_req.payload_byte_count();
        if (rx_bytes != LOOPBACK_BYTES) begin
            `uvm_error("USB_DEV0_HOTPLUG_SEQ",
                $sformatf({"%s loopback check FAILED: received %0d of %0d ",
                           "bytes after the full device_timeout retry budget. ",
                           "This is a PERMANENT endpoint stall, not an early ",
                           "IN: an un-armed endpoint NAKs and the host retries. ",
                           "Look for a missing \"EP1 IN armed\" line in the MCU ",
                           "log and for a data_toggle_check_* error (a toggle ",
                           "mismatch is ACKed and discarded, so the endpoint ",
                           "goes dead silently)."},
                          dev_name, rx_bytes, LOOPBACK_BYTES))
            return;
        end

        for (int unsigned bi = 0; bi < LOOPBACK_BYTES; bi++) begin
            if (in_req.payload.data[bi] !== sent[bi]) begin
                `uvm_error("USB_DEV0_HOTPLUG_SEQ",
                    $sformatf("%s loopback mismatch at byte[%0d]: sent=0x%02h received=0x%02h",
                              dev_name, bi, sent[bi], in_req.payload.data[bi]))
                mismatch_count++;
            end
        end

        if (mismatch_count == 0)
            `uvm_info("USB_DEV0_HOTPLUG_SEQ",
                $sformatf("%s loopback data check PASSED: all %0d bytes match.",
                          dev_name, LOOPBACK_BYTES), UVM_LOW)
        else
            `uvm_error("USB_DEV0_HOTPLUG_SEQ",
                $sformatf("%s loopback data check FAILED: %0d byte(s) mismatched.",
                          dev_name, mismatch_count))
    endfunction

endclass

`endif // CALIPTRA_SS_USB_DUAL_DEVICE_HS_DEV0_HOTPLUG_SEQUENCE_SV
