// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

`ifndef CALIPTRA_SS_USB_HS_DEV_HIGH_BANDWIDTH_ISO_TEST_SV
`define CALIPTRA_SS_USB_HS_DEV_HIGH_BANDWIDTH_ISO_TEST_SV

// Configures EP2 IN for three high-speed ISO transactions per microframe.
class caliptra_ss_usb_hs_dev_high_bandwidth_iso_test
    extends caliptra_ss_usb_base_test;

    `uvm_component_utils(
        caliptra_ss_usb_hs_dev_high_bandwidth_iso_test)

    function new(
        string name = "caliptra_ss_usb_hs_dev_high_bandwidth_iso_test",
        uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("USB_SS_HB_ISO_TEST", "Configuring subsystem HB ISO test", UVM_LOW)
        super.build_phase(phase);

        cfg.dev_cfg.local_device_cfg[0].num_endpoints = 2;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number = 2;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction =
            svt_usb_types::IN;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type =
            svt_usb_types::ISOCHRONOUS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].interval = 1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_burst_size = 0;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size =
            1024;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].isoc_mult =
            svt_usb_endpoint_configuration::ISOC_MULT_TWO;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].
            usb_20_isoc_without_first_last_transaction = 1'b1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed =
            svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].device_timeout = 20ms;

        uvm_config_db#(uvm_object_wrapper)::set(
            this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            caliptra_ss_usb_hs_dev_high_bandwidth_iso_sequence::type_id::get());
    endfunction

    virtual function time get_mcu_halt_timeout();
        return 20ms;
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_HIGH_BANDWIDTH_ISO_TEST_SV
