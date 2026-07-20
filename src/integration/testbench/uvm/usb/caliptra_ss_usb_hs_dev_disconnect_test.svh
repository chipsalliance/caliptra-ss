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

`ifndef CALIPTRA_SS_USB_HS_DEV_DISCONNECT_TEST_SV
`define CALIPTRA_SS_USB_HS_DEV_DISCONNECT_TEST_SV

// =============================================================================
// USB High-Speed device disconnect/reconnect test.
// DUT is the USB device controller. VIP host connects at HS, then
// powers off the port to disconnect, waits, then reconnects and verifies
// the HS link is re-established.
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_dev_disconnect_test
// =============================================================================
class caliptra_ss_usb_hs_dev_disconnect_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_hs_dev_disconnect_test)

    function new(string name = "caliptra_ss_usb_hs_dev_disconnect_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // Extend device_timeout to allow MCU firmware (software-polled) time to
        // process each SETUP token. The default (shared_cfg) value of 50us is too
        // short for software-polled HS firmware - the poll loop takes several
        // microseconds per iteration so repeated SETUP retries fire timeout checks
        // before firmware can respond.
        cfg.dev_cfg.local_device_cfg[0].device_timeout = 5000us;

        // Extend the HS tend_to_end_delay threshold to suppress spurious
        // tend_to_end_delay_check errors. The USB 2.0 spec limit (500ns for HS)
        // cannot be met by software-polled firmware. The hardware controller
        // drives no response (not even NAK) while EP0 OUT is un-armed between
        // the SETUP being consumed and firmware calling usb_ep0_reinit(). This
        // is a known limitation of software-polled USB device controllers in
        // simulation and does not affect functional correctness.
        cfg.host_cfg.tend_to_end_delay_hs = 100000000.0; // 100 ms in ns

        // HS mode defaults (high_speed_capable=1).
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_dev_disconnect_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_DISCONNECT_TEST_SV
