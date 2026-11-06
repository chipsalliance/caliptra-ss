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

`ifndef CALIPTRA_SS_USB_HS_DEV_VBUS_ABSENT_BOOT_TEST_SV
`define CALIPTRA_SS_USB_HS_DEV_VBUS_ABSENT_BOOT_TEST_SV

// =============================================================================
// USB High-Speed "VBus absent at boot" test.
//
// Covers the self-powered-device bring-up ordering: the SoC boots, enables its
// hub and requests an upstream connect with no host attached, and only later
// does the host appear. Every other USB test has VBus up before firmware
// touches the USB core, so this ordering is otherwise unexercised.
//
// The ONLY cfg difference from a plain HS test is poweron_auto_attach_delay.
// Everything else - HS defaults, endpoint stamping, the link-up timers - is
// inherited unchanged from caliptra_ss_usb_shared_cfg. In particular no
// endpoint re-stamp is needed (that is an FS-variant requirement) and no
// testbench change is needed: VBus already starts at 0 in every run, the VIP
// drives it, and caliptra_ss_usb_vbus_driver.sv forwards it to the DUT pin.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_dev_vbus_absent_boot_test
// =============================================================================
class caliptra_ss_usb_hs_dev_vbus_absent_boot_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_hs_dev_vbus_absent_boot_test)

    // -------------------------------------------------------------------------
    // When the VIP powers on its port and attaches, in ps.
    //
    // This single value is what creates the whole scenario. The shared cfg
    // default is 20 us (USB_TIMER_20US_PS), which fires ~12 us BEFORE firmware
    // even begins boot_usb_core_hub() - that is why no existing test sees a
    // VBus-absent bring-up.
    //
    // Sizing is measured, not guessed. Across all 41 HS tests of
    // caliptra_nightly_regression_2026_10_24_05_31_55, the timestamp of the
    // firmware log line "HUB_CTRL after HUB_CONNECT=1" was:
    //     min 55.3 us, max 69.5 us, mean 59.9 us
    // bimodal: most tests land 55-59 us, while the descriptor-override family
    // (hs_dev_get_* / hub_*descriptor / hub_qualifier) lands at 69.2-69.5 us.
    //
    // 150 us is ~2.2x the worst observed case, so firmware has always
    // completed HUB_EN + HUB_CONNECT with VBus still low before the host
    // arrives. If a future boot path ever drifts past 150 us the firmware's
    // Phase 0a check fails loudly ("VBUS_DEBOUNCED already set before USB
    // bring-up") rather than silently degenerating into the ordinary
    // always-VBus-present scenario that every other test already covers.
    //
    // NOTE: keep in sync with vbus_attach_delay_us in
    // caliptra_ss_usb_hs_dev_vbus_absent_boot_sequence.svh, which uses it to
    // size its negative window and its attach timeout.
    localparam real VBUS_ATTACH_DELAY_PS = 150000000.0;  // 150 us

    function new(string name = "caliptra_ss_usb_hs_dev_vbus_absent_boot_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // HS: leave high_speed_capable at its default so the VIP performs the
        // chirp handshake. The firmware asserts DEVCMDSTAT.SPEED == HS after
        // enumeration, which is the real point of running this as the HS
        // variant: a late attach is where a missed chirp would show up.
        //
        // Defer the attach on BOTH cfgs. host_cfg is the VIP host that powers
        // the port; dev_cfg is cloned into remote_cfg as the device-side PHY
        // model. Leaving dev_cfg at 20 us would have the device PHY attach
        // while the host has not yet powered up, which is not a state a real
        // link can be in.
        cfg.host_cfg.poweron_auto_attach_delay = VBUS_ATTACH_DELAY_PS;
        cfg.dev_cfg.poweron_auto_attach_delay  = VBUS_ATTACH_DELAY_PS;

        `uvm_info("build_phase",
            $sformatf({"VBus-absent-at-boot: deferred VIP auto-attach to ",
                       "%0.1f us on host_cfg and dev_cfg (shared_cfg default ",
                       "is 20 us). Firmware reaches HUB_CONNECT at 55-70 us, ",
                       "so it brings the hub up with no VBus present."},
                      VBUS_ATTACH_DELAY_PS / 1000000.0),
            UVM_LOW)

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_dev_vbus_absent_boot_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_VBUS_ABSENT_BOOT_TEST_SV
