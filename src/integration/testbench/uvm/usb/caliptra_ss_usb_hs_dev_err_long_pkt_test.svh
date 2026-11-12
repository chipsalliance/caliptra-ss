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

`ifndef CALIPTRA_SS_USB_HS_DEV_ERR_LONG_PKT_TEST_SV
`define CALIPTRA_SS_USB_HS_DEV_ERR_LONG_PKT_TEST_SV

// =============================================================================
// caliptra_ss_usb_hs_dev_err_long_pkt: USB error-injection test, High Speed, USBDC0.
//
// Stimulus for usb_transfer_outcome_cg.cp_errortype bins overrun (0xB)
// of src/usb/coverage/usb_dev_ep_cov.sv. Those bins were at zero because
// nothing in the regression ever corrupted a packet; see the sequence header
// for the RTL assignment site each one is driven from.
//
// THE EP1 CONFIGURATION IS COPIED FROM caliptra_ss_usb_hs_dev_bulk_out_test
//
// The error-injection sequences drive a bulk OUT on EP1, so the VIP needs the
// same EP1 model that test declares, for the same reasons:
//   - allow_aligned_transfer_without_zero_length = 1 because the NXP IP_3516
//     firmware never appends a ZLP after a max-packet-aligned bulk OUT, and
//     without it the VIP sends one that firmware NAKs until the transfer
//     ABORTs.
//   - device_timeout is left at the long 5000 us value because an injected
//     error can legitimately leave a transfer unanswered - a bad-CRC data
//     packet gets no handshake at all - and the sequence relies on the VIP
//     ending that transfer rather than the test dying on a short timeout.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_long_pkt_test
// =============================================================================
class caliptra_ss_usb_hs_dev_err_long_pkt_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_hs_dev_err_long_pkt_test)

    function new(string name = "caliptra_ss_usb_hs_dev_err_long_pkt_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        caliptra_ss_usb_hs_dev_err_length_sequence seq;

        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // HS mode: leave high_speed_capable at its default so the VIP chirps.
        cfg.host_cfg.speed = svt_usb_types::HS;
        cfg.dev_cfg.speed  = svt_usb_types::HS;

        // EP1 BULK OUT at HS, 512-byte max packet.
        cfg.dev_cfg.local_device_cfg[0].device_timeout            = 5000us;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed     = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size =
            `SVT_USB_HS_BULK_MAX_PACKET_SIZE;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].allow_aligned_transfer_without_zero_length = 1;

        // The sequence is built here rather than installed by type so the
        // error selector below can be set on the instance. build_phase is the
        // correct place for that - see the note in caliptra_ss_usb_base_sequence
        // pre_start() on why the data-check handle is resolved later.
        seq = caliptra_ss_usb_hs_dev_err_length_sequence::type_id::create("seq");
        seq.length_target = svt_usb_packet_exception::LONG_PACKET_ERROR;
        uvm_config_db#(uvm_sequence_base)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence", seq);

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_ERR_LONG_PKT_TEST_SV

// File contains AI-generated response based on internal company sources
