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

`ifndef CALIPTRA_SS_USB_DUAL_DEVICE_HS_DEV0_HOTPLUG_TEST_SV
`define CALIPTRA_SS_USB_DUAL_DEVICE_HS_DEV0_HOTPLUG_TEST_SV

// =============================================================================
// USB dual-device High-Speed DEV0 hotplug isolation test.
//
// Verifies that USBDC0 connect/disconnect activity on hub downstream port 1
// does not perturb USBDC1 while USBDC1 is actively running EP1 bulk loopback
// traffic on hub downstream port 2:
//   - USBDC0 : hub downstream port 1, USB device address 2, PIC vector 3.
//              Cycled through 3 disconnect/reconnect iterations by firmware
//              toggling DEVCMDSTAT.DCON.
//   - USBDC1 : hub downstream port 2, USB device address 3, PIC vector 6
//              (wired via the TB loopback gated by USB_HUB_COMPOUND_DEV1_IRQ).
//              Runs a repeating EP1 64-byte bulk OUT -> IN loopback throughout.
//
// This is a longer-running test than the plain dual-device bulk loopback: each
// hotplug cycle includes a full USBDC0 re-enumeration plus hub port-1 status
// polling, so the device_timeout and HS end-to-end delay thresholds are raised
// relative to caliptra_ss_usb_dual_device_hs_bulk_loopback_test.
//
// REMOTE-DEVICE MODELLING. This test gives EVERY device on the bus its own
// PERSISTENT host_cfg.remote_device_cfg[] slot, created once in build_phase
// via caliptra_ss_usb_shared_cfg::add_remote_device_slot():
//   slot 0 - device_address 0 (the default address a device answers on
//            between a hub port reset and SET_ADDRESS)
//   slot 1 - hub,    device_address 1
//   slot 2 - USBDC0, device_address 2
//   slot 3 - USBDC1, device_address 3
// Transfers select their target with the dev_anchor_idx argument, so no slot
// is ever retargeted and reconfigure() is never called after bring-up.
//
// This replaced a single-slot design in which the sequence retargeted
// remote_device_cfg[0].device_address and called reconfigure() before every
// transfer. reconfigure() rebuilds EVERY endpoint protocol processor on the
// agent, and a freshly built BULK endpoint restarts its DATA TOGGLE at DATA0;
// USB 2.0 section 8.6 then makes the device DISCARD the next OUT as a presumed
// retransmission, silently - no buffer write, no completion interrupt. The
// measured USBDC1 EP1 BULK OUT PIDs were DATA0, DATA1, DATA0, DATA0 with the
// fourth needing to be DATA1, which is precisely why three loopbacks passed
// and the fourth killed the endpoint. The full evidence table lives in
// caliptra_ss_usb_shared_cfg::add_remote_device_slot.
//
// Each slot carries its own copy of the same 3-endpoint layout (EP0 CTRL,
// EP1 BULK IN, EP1 BULK OUT) configured below on slot 0 and cloned from it.
//
// endpoint_cfg[] is an array INDEX, not the USB endpoint number:
//   endpoint_cfg[0] ep_number=0 direction=IN  CONTROL  (shared_cfg default)
//   endpoint_cfg[1] ep_number=1 direction=IN  BULK IN  (shared_cfg default)
//   endpoint_cfg[2] ep_number=1 direction=OUT BULK OUT (allocated here)
// The sequence passes these as ep_anchor_idx: 2 for bulk OUT, 1 for bulk IN.
//
// Firmware (caliptra_ss_usb_dual_device_hs_dev0_hotplug.c) MUST be built with
// -DUSB_HUB_COMPOUND_DEV1_IRQ and MUST NOT be built with -DUSB_DEV_SEL=1
// (it addresses both apertures at runtime via usb_select_device()).
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_dual_device_hs_dev0_hotplug_test
//   +USB_HUB_COMPOUND_DEV1_IRQ=1
// =============================================================================
class caliptra_ss_usb_dual_device_hs_dev0_hotplug_test
    extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_dual_device_hs_dev0_hotplug_test)

    function new(string name = "caliptra_ss_usb_dual_device_hs_dev0_hotplug_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Indices of the persistent remote_device_cfg[] slots created in
    // build_phase, one per bus address. Published via the config_db for the
    // sequence to pick up. Slot 0 is the pre-existing entry and stays at
    // device_address 0, the default address a device answers on between a hub
    // port reset and SET_ADDRESS.
    int hub_anchor_idx;
    int usbdc0_anchor_idx;
    int usbdc1_anchor_idx;

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // HS mode. high_speed_capable defaults to 1 (shared_cfg) so the VIP
        // drives the HS chirp. The thresholds below are deliberately larger
        // than the plain dual-device loopback test: this test performs 3 full
        // USBDC0 re-enumerations interleaved with USBDC1 traffic and with hub
        // port-status polling, all against software-polled firmware.
        // device_timeout is the whole-transfer abort deadline - per the VIP
        // source, svt_usb_device_configuration::device_timeout is the time
        // "after which Host will abort a transfer". It does NOT bound how many
        // times a NAKed transaction is re-tried; that is a separate,
        // count-based budget (max_retry_due_to_nak, applied via
        // USB_EP_MAX_RETRY_DUE_TO_NAK in caliptra_ss_usb_shared_cfg).
        //
        // It is kept large here because it is the per-transfer cost of a
        // genuinely dead device and is paid once per retry: with 20 ms, a
        // single wedged control transfer cost 4 x 20 ms = 80 ms of simulation
        // on its own (run killed at 85.73 ms / 17.8 h of CPU, with the last
        // 84 ms containing nothing but those retries). 2 ms keeps that
        // pathology bounded while leaving ample room for the slowest response
        // this software-polled firmware produces.
        cfg.dev_cfg.local_device_cfg[0].device_timeout = 2000us;
        cfg.host_cfg.tend_to_end_delay_hs              = 400000000.0; // 400 ms in ns
        cfg.host_cfg.speed                             = svt_usb_types::HS;
        cfg.dev_cfg.speed                              = svt_usb_types::HS;

        // Extend to 3 endpoint entries so index 2 (EP1 BULK OUT) is valid.
        // shared_cfg default allocates 2 ([0]=EP0 CTRL, [1]=EP1 BULK IN).
        cfg.dev_cfg.local_device_cfg[0].num_endpoints   = 3;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2] = new();

        // endpoint_cfg[0]: EP0 CONTROL (HS).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].speed           = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size =
            `SVT_USB_HS_CONTROL_MAX_PACKET_SIZE;

        // endpoint_cfg[1]: EP1 BULK IN (device sends loopback data to host).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number       = 1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction       = svt_usb_types::IN;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type         = svt_usb_types::BULK;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed           = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size =
            `SVT_USB_HS_BULK_MAX_PACKET_SIZE;

        // endpoint_cfg[2]: EP1 BULK OUT (host sends data to device).
        // allow_aligned_transfer_without_zero_length=1: the NXP IP_3511 firmware
        // never appends a ZLP after a max-packet-aligned bulk OUT. Without this
        // the VIP constraint fixed_dev_ep_ustr_valid_ranges forces a trailing
        // ZLP the firmware NAKs, eventually ABORTing the transfer.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].ep_number       = 1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].direction       = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].ep_type         = svt_usb_types::BULK;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].speed           = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].max_packet_size =
            `SVT_USB_HS_BULK_MAX_PACKET_SIZE;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].allow_aligned_transfer_without_zero_length = 1;

        // endpoint_cfg[2] was allocated above, after shared_cfg had already
        // run, so it still carries the VIP default max_retry_due_to_nak of 10.
        // Re-apply the shared budget now that every endpoint object exists.
        cfg.apply_nak_retry_budget();

        // ------------------------------------------------------------------
        // Persistent per-device remote_device_cfg[] slots.
        //
        // These MUST be created after the endpoint_cfg[] layout above:
        // add_remote_device_slot() clones slot 0's endpoints, so slot 0 has to
        // be complete (all three endpoints, correct packet sizes, the
        // allow_aligned_transfer_without_zero_length flag and the NAK budget)
        // before any clone is taken.
        //
        // WHY THEY EXIST. Previously ONE slot described every device in turn,
        // so the sequence had to retarget it between transfers with
        // remote_device_cfg[0].device_address = addr + reconfigure(). That
        // retarget is destructive: reconfigure() rebuilds EVERY endpoint
        // protocol processor on the agent and a freshly built BULK endpoint
        // restarts its DATA TOGGLE at DATA0, which USB 2.0 section 8.6 turns
        // into a SILENT data loss on the next OUT. The measured BULK OUT PID
        // sequence on USBDC1 EP1 was DATA0, DATA1, DATA0, DATA0 where the
        // fourth had to be DATA1 - the first transfer at which the reset was
        // observable at all, and hence why exactly three loopbacks passed
        // before the endpoint went dead. Full evidence table in
        // caliptra_ss_usb_shared_cfg::add_remote_device_slot.
        //
        // With one persistent slot per bus address nothing is ever retargeted,
        // no reconfigure() is needed after bring-up, every endpoint xactor
        // lives for the whole run, and the toggles advance continuously the
        // way they do against a real host.
        //
        // Slot 0 keeps device_address 0, which is what a device answers on
        // after a hub port reset and before SET_ADDRESS, so it serves every
        // enumeration's default-address stage.
        //
        // The slot indices are published through the config_db rather than
        // hardcoded in the sequence so the two cannot drift apart.
        hub_anchor_idx    = cfg.add_remote_device_slot(7'd1); // hub
        usbdc0_anchor_idx = cfg.add_remote_device_slot(7'd2); // USBDC0
        usbdc1_anchor_idx = cfg.add_remote_device_slot(7'd3); // USBDC1

        // Context must be null, not "this". A set(this, "*", ...) stores the
        // entry under the scope "uvm_test_top.*", which matches neither the
        // exact scope "uvm_test_top" nor the wildcard "*" that the sequence
        // uses to read it back, so the get() returned 0 and tripped a
        // uvm_fatal. The sequence runs on the host agent virtual sequencer,
        // which is not a child of this test, so a test-relative scope cannot
        // reach it. Publishing with a null context stores under the global
        // scope "*", which is the pattern already proven by usb_int_ep_num in
        // caliptra_ss_top_tb_services.sv and read by
        // caliptra_ss_usb_hs_dev_int_loopback_sequence.svh.
        uvm_config_db#(int)::set(null, "*", "hub_anchor_idx",    hub_anchor_idx);
        uvm_config_db#(int)::set(null, "*", "usbdc0_anchor_idx", usbdc0_anchor_idx);
        uvm_config_db#(int)::set(null, "*", "usbdc1_anchor_idx", usbdc1_anchor_idx);


        `uvm_info("build_phase",
            $sformatf({"Persistent remote-device slots: addr0=0 hub=%0d ",
                       "usbdc0=%0d usbdc1=%0d (remote_device_cfg_size=%0d)."},
                      hub_anchor_idx, usbdc0_anchor_idx, usbdc1_anchor_idx,
                      cfg.host_cfg.remote_device_cfg_size), UVM_LOW)

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_dual_device_hs_dev0_hotplug_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

    // Cap how long the run_phase will wait for the MCU to halt.
    //
    // The base test's phase_ready_to_end() raises a run_phase objection and
    // holds it until bfm_if.mcu_halt_status asserts, i.e. until the firmware
    // reaches csr_write_mpmc_halt() at the end of main(). The host sequence
    // finishing does NOT end the simulation - the MCU does. The base default of
    // 100 ms is therefore the real cost of any firmware hang, and it is what
    // produced the ~6.9 ms run whose last 5.5 ms contained no activity at all.
    //
    // The firmware self-limits to USB_TEST_RUN_BUDGET_US = 4000 us of polling
    // before printing its verdict and halting. That budget was resized upwards
    // (from 1400 us) once the hotplug FSM was made to wait for real host
    // evidence: a healthy disconnect/reconnect cycle costs ~600 us of wall
    // clock, so three cycles plus the initial enumeration need ~2.6 ms. The
    // verdict print itself is a few tens of us (VPRINTF pushes one character
    // per ~28.6 ns at CALIPTRA_SS_CLK_FREQ = 400 MHz), and the halt handshake
    // is immediate after it.
    //
    // 5 ms therefore still sits ~1 ms above the firmware's own self-limit and
    // above the host sequence's ~2.3 ms worst case, while making a firmware
    // that never halts cost 5 ms instead of 100 ms. If USB_TEST_RUN_BUDGET_US
    // is ever raised again, this bound MUST be raised with it - the firmware
    // budget has to expire first, because its verdict line is the only thing
    // that explains WHY the run ended.
    //
    // NOTE: this bound is NOT sufficient on its own - see RUN_WATCHDOG below.
    // phase_ready_to_end() only runs once every other objection on the phase
    // has dropped, so a host sequence that never returns keeps this timeout
    // permanently out of reach.
    virtual function time get_mcu_halt_timeout();
        return 5_000_000ns; // 5 ms
    endfunction

    // Absolute wall-clock bound on the whole run.
    //
    // WHY A SECOND TIMEOUT IS NEEDED. Every other bound in this test is
    // conditional on something completing:
    //   - get_mcu_halt_timeout() is armed from phase_ready_to_end(), which UVM
    //     calls only after all other objections on the phase have dropped, so a
    //     host sequence that never returns disarms it entirely;
    //   - PORT_POLL_MAX_ATTEMPTS bounds the sequence's port polling loops, but
    //     not the control transfers issued after them;
    //   - device_timeout bounds one transaction, and is paid per retry.
    // With all three in place a run still reached 85.73 ms of simulated time
    // and 17.8 hours of CPU and had to be killed by hand: the MCU halted at
    // 1.586 ms, and the host then spent 84 ms retrying a GET_DESCRIPTOR against
    // a device the firmware had disconnected for good. Nothing in the testbench
    // was watching the clock.
    //
    // This watchdog is unconditional by construction - a bare delay in
    // run_phase, forked before anything else can block - and it reports via
    // uvm_fatal so the run still produces a UVM report summary instead of a
    // bare $finish. 10 ms is roughly 2x get_mcu_halt_timeout() and ~7x the
    // firmware's own budget, so it can only ever fire on a real hang.
    localparam time RUN_WATCHDOG = 10_000_000ns; // 10 ms

    virtual task run_phase(uvm_phase phase);
        fork
            begin : run_watchdog
                #RUN_WATCHDOG;
                `uvm_error("USB_DEV0_HOTPLUG_TEST",
                    $sformatf({"RUN WATCHDOG expired after %0t with the run ",
                               "still in progress. Neither the MCU halt ",
                               "handshake nor the host sequence completed. ",
                               "Check the tail of the log for a transfer being ",
                               "retried against a disconnected device, and the ",
                               "MCU log for its last verdict line."},
                              RUN_WATCHDOG))
                `uvm_fatal("USB_DEV0_HOTPLUG_TEST",
                           "RUN WATCHDOG expired - terminating the simulation")
            end
        join_none

        super.run_phase(phase);
    endtask

endclass

`endif // CALIPTRA_SS_USB_DUAL_DEVICE_HS_DEV0_HOTPLUG_TEST_SV
