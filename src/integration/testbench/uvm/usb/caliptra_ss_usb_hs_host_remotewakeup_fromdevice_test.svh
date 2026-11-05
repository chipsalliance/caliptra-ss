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

`ifndef CALIPTRA_SS_USB_HS_HOST_REMOTEWAKEUP_FROMDEVICE_TEST_SV
`define CALIPTRA_SS_USB_HS_HOST_REMOTEWAKEUP_FROMDEVICE_TEST_SV

// =============================================================================
// USB HS device-initiated remote wakeup test.
//
// Usage: +UVM_TESTNAME=caliptra_ss_usb_hs_host_remotewakeup_fromdevice_test
//        plus +usb_suspend_resume_check=1 and +usb_device_wakeup_check=1 (both
//        set by the test yml).
//
// Device-initiated, host-completed remote wakeup against the hub-composite IP.
// Verdict is CHK_DEVICE_WAKEUP_K in caliptra_ss_usb_device_wakeup_checker, not
// any VIP status field.
// =============================================================================

class caliptra_ss_usb_hs_host_remotewakeup_fromdevice_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_hs_host_remotewakeup_fromdevice_test)

    function new(string name = "caliptra_ss_usb_hs_host_remotewakeup_fromdevice_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // tinactivity is deliberately NOT overridden. It must stay at its
        // shared default or the VIP link never declares SUSPENDED and
        // clear_suspend is discarded silently. The firmware side matches by
        // calling boot_usb_core_hub().

        // tdrsmdn is the VIP RESUMING -> SEND_EOR dwell, i.e. how long the host
        // holds resume K before terminating it with the low-speed EOP. It is set
        // HERE and not from the sequence: a mid-run reconfigure() of this field
        // was measured delivering 28.03 us against 3.2 ms requested, so the
        // write did not reach the running link SM.
        //
        // The value must outlast the DUT's own resume K, because
        // BUS_EVENT_SW_WAKEUP_3 only leaves on an SE0 and has no timeout arm, so
        // an EOP driven before that state opens is simply lost. On the L2 path
        // the device drives K for T_3ms (3.072 ms) and then takes T_TxENDDELAY
        // (30 us) through SW_WAKEUP_2, so the window opens ~3.102 ms after the
        // first K bit. 3.2 ms clears that with ~98 us to spare.
        //
        // Do NOT copy the 200 us used by caliptra_ss_usb_hs_dev_lpm_l1: that
        // path drives K for T_60us, not T_3ms (usb_pie.m.vhdl:1503 vs 1372), so
        // its window opens ~90 us in. Both paths then converge on the SAME
        // BUS_EVENT_SW_WAKEUP_2/_3 states (see the RTL comment at
        // usb_pie.m.vhdl:1511), which is why only this one timer differs.
        cfg.host_cfg.tdrsmdn = 3_200_000_000.0; // 3.2 ms in ps

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_host_remotewakeup_fromdevice_sequence::type_id::get());
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_HOST_REMOTEWAKEUP_FROMDEVICE_TEST_SV
