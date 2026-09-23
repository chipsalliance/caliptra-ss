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

`ifndef CALIPTRA_SS_USB_FS_HOST_REMOTEWAKEUP_FROMDEVICE_TEST_SV
`define CALIPTRA_SS_USB_FS_HOST_REMOTEWAKEUP_FROMDEVICE_TEST_SV

// =============================================================================
// USB FS device-initiated remote wakeup test.
//
// Usage: +UVM_TESTNAME=caliptra_ss_usb_fs_host_remotewakeup_fromdevice_test
//        plus +usb_suspend_resume_check=1 and +usb_device_wakeup_check=1 (both
//        set by the test yml).
//
// This is the only test in which the resume is STARTED by the device rather than
// by the host. Remote wakeup is device-initiated and host-completed, so both
// halves appear here:
//
//   device half  the MCU firmware requests the wakeup and USBDC0 drives resume
//                K upstream. This is the feature under test, and the verdict on
//                it is CHK_DEVICE_WAKEUP_K in
//                caliptra_ss_usb_device_wakeup_checker, which watches the DUT
//                assert UTMI TXValid with linestate=K. TXValid is a DUT output,
//                so no host activity can forge that check.
//   host half    the sequence then drives
//                svt_usb_link_service_clear_suspend_sequence, but only AFTER the
//                device K has been observed. The host must terminate the resume
//                with a low-speed EOP or the peripheral engine parks in
//                BUS_EVENT_SW_WAKEUP_3 forever (usb_pie.m.vhdl, no timeout arc).
//
// svt_usb_status::device_remote_wakeup_in_progress is only logged, not checked:
// it was measured staying 0 through a full, correct device K. See the test
// README and docs/usb_remote_wakeup_selfclear_race_report.md sections 2A.4, 7.4
// and 7.5.

// =============================================================================

class caliptra_ss_usb_fs_host_remotewakeup_fromdevice_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_fs_host_remotewakeup_fromdevice_test)

    function new(string name = "caliptra_ss_usb_fs_host_remotewakeup_fromdevice_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // ---------------------------------------------------------------
        // FS conversion block, same as the FS global_suspend_L2 test. Puts the
        // VIP into FS-only mode and re-stamps the default endpoints to FS so
        // cfg.is_valid() passes (see claude_md/02_tests.md section 6). The
        // widened FS-link timing knobs keep the link alive through enumeration
        // in scaledown simulation.
        // ---------------------------------------------------------------
        cfg.host_cfg.local_host_cfg.high_speed_capable        = 0;
        cfg.host_cfg.speed                                    = svt_usb_types::FS;
        cfg.dev_cfg.speed                                     = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].connected_bus_speed   = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].functionality_support = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].device_timeout        = 5000us;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size = `SVT_USB_FS_CONTROL_MAX_PACKET_SIZE;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size = `SVT_USB_FS_BULK_MAX_PACKET_SIZE;
        cfg.host_cfg.tddis = 2_000_000_000; // 2 ms in ps (int32-safe, > 1ms FS SOF)
        cfg.dev_cfg.tddis  = 2_000_000_000;
        cfg.host_cfg.tend_to_end_delay_fs = 2_000_000_000.0; // 2 ms in ps
        cfg.dev_cfg.tend_to_end_delay_fs  = 2_000_000_000.0;
        // tinactivity is how long the VIP host link waits on an idle bus before
        // it declares SUSPENDED, and in THIS test it is a correctness
        // constraint rather than a performance knob.
        //
        // The VIP only recognises an upstream K as a remote wakeup, and only
        // sets svt_usb_status::device_remote_wakeup_in_progress, if its own
        // link is already suspended when the K arrives. So the VIP must reach
        // SUSPENDED strictly BEFORE the device drives K. Measured ordering with
        // the previous 2 ms value, relative to the SOF-off at 1.4199 ms:
        //
        //   DUT suspends (T_SUSPEND_DET_FS 1100 us + T_TWTRSTHS)  2.9293 ms
        //   firmware arms and the device drives K (~90 us later)  3.0167 ms
        //   VIP would have declared SUSPENDED (1.4199 + 2 ms)     3.4199 ms
        //
        // The device therefore woke a link the VIP still considered ENABLED,
        // the status bit was never set, and the test failed while the DUT had
        // in fact behaved correctly (the checker scored both SuspendM edges).
        //
        // The window is bounded on both sides:
        //   lower bound: > 1 ms, the FS SOF period, or the link would declare
        //                SUSPENDED in the normal gap between two SOFs;
        //   upper bound: < ~1500 us, the DUT's own suspend-detect latency, or
        //                the device wakes before the VIP has suspended.
        // 1.2 ms sits inside that window with about 300 us of margin on the
        // side that matters. Note this is the FS timer: T_SUSPEND_DET_SIM_FS is
        // 1100 us (usb_pie.m.vhdl:508), NOT the 200 us HS value, so an HS
        // variant of this test would need a different figure.
        cfg.host_cfg.tinactivity = 1_200_000_000.0; // 1.2 ms in ps
        cfg.dev_cfg.tinactivity  = 1_200_000_000.0;


        cfg.host_cfg.drive_reset_time = 150_000_000; // 150 us in ps

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_fs_host_remotewakeup_fromdevice_sequence::type_id::get());
    endfunction

endclass

`endif // CALIPTRA_SS_USB_FS_HOST_REMOTEWAKEUP_FROMDEVICE_TEST_SV
