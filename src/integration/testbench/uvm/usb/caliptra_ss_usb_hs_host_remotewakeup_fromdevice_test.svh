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
//
// Design notes, flow, constant derivations and the tinactivity rationale live
// in a single note. Read it before changing anything here:
//   caliptra_ss_nxp_dv_accessories/docs/handover/claude_md/
//       25_usb_remotewakeup_fromdevice_design_notes.md
// The FS -> HS port record is note 24 of the same directory.
// =============================================================================

class caliptra_ss_usb_hs_host_remotewakeup_fromdevice_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_hs_host_remotewakeup_fromdevice_test)

    function new(string name = "caliptra_ss_usb_hs_host_remotewakeup_fromdevice_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // The FS variant's speed-conversion block is deliberately absent:
        // caliptra_ss_usb_shared_cfg.svh already defaults the environment to
        // high speed, so the correct HS configuration is the one obtained by
        // NOT overriding anything. The firmware side matches by calling
        // boot_usb_core_hub() rather than boot_usb_core_fs(). Note 25 section 8.

        // tinactivity is relaxed here for enumeration only; the tight
        // suspend-window value is applied by the sequence immediately before
        // SOF-off. The tight value must not be in force during enumeration or
        // SET_ADDRESS is never granted the link. Keep the two in sync.
        // Note 25 section 6.
        cfg.host_cfg.tinactivity = 10_000_000_000.0; // 10 ms in ps, enumeration phase
        cfg.dev_cfg.tinactivity  = 10_000_000_000.0;

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_host_remotewakeup_fromdevice_sequence::type_id::get());
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_HOST_REMOTEWAKEUP_FROMDEVICE_TEST_SV

// File contains AI-generated response based on internal company sources
