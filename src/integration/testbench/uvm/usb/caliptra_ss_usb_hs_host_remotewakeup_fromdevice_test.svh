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
        // holds resume K before terminating it with the low-speed EOP. It is
        // deliberately NOT overridden, and must not be.
        //
        // SVT_USB_TDRSMDN_MIN == SVT_USB_TDRSMDN_NOM == 20 ms with no MAX
        // (svt_usb_timing_defines.svi:21-22), so any smaller value sits below
        // the VIP floor and is rejected. An earlier 3.2 ms override here was
        // measured producing a 28.03 us dwell on the wire, and the host then
        // never drove a terminating SE0 at all.
        //
        // The untouched 20 ms default is already longer than the DUT needs: on
        // the L2 path the device drives K for T_3ms (3.072 ms) and reaches
        // BUS_EVENT_SW_WAKEUP_3 about T_TxENDDELAY (30 us) later, so the SE0
        // lands inside that window with ~17 ms to spare. Measured on the
        // 2026-11-05 run: window opens 4569.680 us, SE0 at 4675.809 us.
        //
        // Do NOT copy the 200 us from caliptra_ss_usb_hs_dev_lpm_l1 either. It
        // is below the same floor and equally inert there; that test passes
        // because its device K is only T_60us (usb_pie.m.vhdl:1503 vs 1372), so
        // the 20 ms default covers it without any override.

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_host_remotewakeup_fromdevice_sequence::type_id::get());
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_HOST_REMOTEWAKEUP_FROMDEVICE_TEST_SV
