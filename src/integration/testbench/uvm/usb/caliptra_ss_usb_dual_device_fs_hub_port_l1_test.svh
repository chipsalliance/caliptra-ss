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

`ifndef CALIPTRA_SS_USB_DUAL_DEVICE_FS_HUB_PORT_L1_TEST_SV
`define CALIPTRA_SS_USB_DUAL_DEVICE_FS_HUB_PORT_L1_TEST_SV

// =============================================================================
// UVM test for per-port hub L1 at FULL SPEED: SetAndTestPortFeature(PORT_L1) on
// downstream port 1 (USBDC0) and port 2 (USBDC1), checking that each port's L1
// state is independent of the other. All stimulus and all checks live in
// caliptra_ss_usb_dual_device_fs_hub_port_l1_sequence; this class installs it
// and re-stamps the VIP for a 12 Mbit/s link.
//
// Requires the dual-device firmware image (both controllers booted), see the
// test's .yml.
//
// Full-speed port of caliptra_ss_usb_dual_device_hs_hub_port_l1_test. The
// stimulus and the per-port checks are speed-independent: PORT_L1 is a hub
// CLASS request carried on EP0, and the hub-side gate it exercises
// (usb_app_hw_hub.m.vhdl, hub_lpm_sup / hub_lpm_data_pending /
// hub_port_lpm_hird_sw) has no speed term at all. What does change is the link
// the request travels over, so every speed-dependent VIP knob has to be
// re-stamped here. The HS twin inherits all of these from the base test's
// defaults and therefore needs no build_phase body beyond installing the
// sequence.
//
// LPM at FS is a real device capability in this IP, not an extrapolation: the
// EXT/LPM token decode in usb_pie.m.vhdl has an explicit
// "if dev_speed_r = USB_FULL_SPEED" branch (it selects INTER_PACKET_DELAY_FS),
// so the controller is expected to accept and act on an LPM transaction while
// the link is running at 12 Mbit/s.
//
// The knob values below are taken from caliptra_ss_usb_dual_device_fs_bulk_-
// loopback_test, which established them against this same firmware and the
// same scaledown preset. This suite is EP0-only (hub class requests plus
// enumeration control transfers) and allocates no extra endpoints, so the
// endpoint_cfg[2] entry and the allow_aligned_transfer_without_zero_length
// workaround from that test do not apply. The two endpoint entries shared_cfg
// does allocate by default must still both be re-stamped: see the comment at
// the endpoint block below.
// =============================================================================

class caliptra_ss_usb_dual_device_fs_hub_port_l1_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_dual_device_fs_hub_port_l1_test)

    function new(string name = "caliptra_ss_usb_dual_device_fs_hub_port_l1_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // FS mode: clear the HS capability so the VIP does not drive the HS
        // chirp during bus reset and both sides settle at 12 Mbit/s. This must
        // agree with the firmware, which calls boot_usb_core_fs() and so sets
        // HUB_CTRL.FORCE_FULLSPEED. Note that control is hub-wide, not
        // per-device: there is no per-port FS forcing, so both downstream
        // devices come up FS together and a mixed-speed variant of this test is
        // not expressible.
        cfg.host_cfg.local_host_cfg.high_speed_capable        = 0;
        cfg.host_cfg.speed                                    = svt_usb_types::FS;
        cfg.dev_cfg.speed                                     = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].connected_bus_speed   = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].functionality_support = svt_usb_types::FS;

        // BOTH default endpoint entries must be re-stamped to FS. Every
        // transfer this suite issues - the enumeration control transfers and
        // the SetAndTestPortFeature(PORT_L1) class requests - rides EP0, and
        // the defaults leave it at HS speed and the HS max-packet-size, which
        // on an FS link makes the VIP emit DATA packets the FS link SM cannot
        // carry. endpoint_cfg[1] carries no traffic here, but shared_cfg still
        // allocates num_endpoints = 2 and leaves that entry as EP1 BULK IN at
        // HS / 512 bytes. 512 is not a legal FS bulk max-packet size, so
        // leaving it alone makes cfg.is_valid() fail in the env build_phase
        // even though the endpoint is never used.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size =
            `SVT_USB_FS_CONTROL_MAX_PACKET_SIZE;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size =
            `SVT_USB_FS_BULK_MAX_PACKET_SIZE;

        // Widen the per-device timeout for the software-polled, interrupt-driven
        // firmware: two controllers are serviced from one polling loop, so a
        // response can be queued behind the other device's servicing.
        cfg.dev_cfg.local_device_cfg[0].device_timeout        = 5000us;

        // tddis: in FS mode the host sends SOF every 1 ms. After a transaction
        // completes the bus is idle until the next SOF frame, and with the
        // scaledown default of 2 us the tddis timer fires during that inter-SOF
        // gap and drives DISCONNECTED, ABORTing the in-progress control
        // transfer. Must exceed the 1 ms FS frame period.
        // NOTE: tddis is a 32-bit integer in ps units, so the maximum is
        // 2,147,483,647 ps (~2.147 ms). 3 ms would overflow to a negative value
        // the VIP rejects; 2 ms fits and still exceeds the SOF period.
        cfg.host_cfg.tddis = 2_000_000_000; // 2 ms in ps
        cfg.dev_cfg.tddis  = 2_000_000_000;

        // tend_to_end_delay_fs: the scaledown preset sets this to ~1.5 us. The
        // interrupt-driven firmware needs far longer than that to decode a
        // SETUP and drive the response, and the VIP protocol scheduler waits
        // for the next SOF boundary before sending the DATA-stage token, so a
        // value at or near the frame period still trips the check just before
        // the token is driven. 2 ms safely clears the FS inter-frame period in
        // scaledown simulation. This is a real type, so the value does not
        // overflow.
        cfg.host_cfg.tend_to_end_delay_fs = 2_000_000_000.0; // 2 ms in ps
        cfg.dev_cfg.tend_to_end_delay_fs  = 2_000_000_000.0;

        // tinactivity: the scaledown preset leaves this at 6.5 us. At FS the
        // inter-token scheduling gap inside a control transfer DATA phase can
        // exceed that, which makes the VIP link SM fire SUSPENDED and ABORT the
        // in-flight transfer. It must also stay longer than the deliberate idle
        // this suite creates while each port sits in L1 - an L1 residency that
        // the VIP mistook for inactivity would be reported as a spurious
        // SUSPENDED and lose the port-independence evidence entirely.
        cfg.host_cfg.tinactivity = 5_000_000_000.0; // 5 ms in ps
        cfg.dev_cfg.tinactivity  = 5_000_000_000.0;

        // drive_reset_time: with high_speed_capable=0 the SVT VIP host goes
        // straight DISCONNECTED->ENABLED without driving SE0. The NXP IP_3511HS
        // requires a bus reset to enter DEFAULT state (addr=0, EP0 armed, UTMI
        // TX enabled), which HS mode gets for free from the mandatory SE0+chirp
        // negotiation. Setting this makes the VIP drive SE0 for the given time
        // before going ENABLED.
        // Units are ps: 150_000_000 ps = 150 us, well above the USB spec tdrst
        // of 10 us. Note 150_000 ps would be only 150 ns, which is NOT long
        // enough for the DUT to register a reset and leaves EP0 uninitialized.
        cfg.host_cfg.drive_reset_time = 150_000_000; // 150 us in ps

        uvm_config_db#(uvm_object_wrapper)::set(
            this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            caliptra_ss_usb_dual_device_fs_hub_port_l1_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_DUAL_DEVICE_FS_HUB_PORT_L1_TEST_SV
