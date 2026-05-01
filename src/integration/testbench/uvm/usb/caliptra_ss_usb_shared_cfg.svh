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

`ifndef CALIPTRA_SS_USB_SHARED_CFG_SV
`define CALIPTRA_SS_USB_SHARED_CFG_SV

`ifndef CALIPTRA_SS_USB_CFG_TIMEOUT
`define CALIPTRA_SS_USB_CFG_TIMEOUT 10ms
`endif

// =============================================================================
// USB shared configuration for Caliptra Subsystem testbench.
//
// This configuration is for a host-only VIP environment where the DUT
// (caliptra_ss_top) acts as the USB device. The VIP host agent uses TLM
// (internal PHY model) and connects to the DUT via the UTMI interface.
//
// Only the host_cfg is instantiated here — there is no VIP device agent.
// The DUT IS the device.
// =============================================================================
class caliptra_ss_usb_shared_cfg extends uvm_object;

    real timeout = `CALIPTRA_SS_USB_CFG_TIMEOUT;

    // Host agent configuration (VIP acts as host)
    svt_usb_agent_configuration host_cfg;

    // Number of endpoints to configure on the remote device (DUT)
    int num_endpoints = 2;

    `uvm_object_utils_begin(caliptra_ss_usb_shared_cfg)
        `uvm_field_object(host_cfg, UVM_ALL_ON|UVM_DEEP)
        `uvm_field_real  (timeout,  UVM_ALL_ON)
        `uvm_field_int   (num_endpoints, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name = "caliptra_ss_usb_shared_cfg");
        super.new(name);

        host_cfg = new();
        host_cfg.component_type = svt_usb_types::HOST;
        host_cfg.top_layer      = svt_usb_agent_configuration::PROTOCOL;

        // Host VIP has a local host function, no local device function
        host_cfg.local_host_cfg          = new();
        host_cfg.local_device_cfg_size   = 0;

        // Remote device config describes the DUT's device capabilities.
        // The host VIP needs this to generate valid transactions.
        host_cfg.remote_device_cfg_size  = 1;
        host_cfg.remote_device_cfg[0]    = new();
        host_cfg.remote_host_cfg         = null;
    endfunction

    // -------------------------------------------------------------------------
    // Setup USB 2.0 HS UTMI defaults for host-only (DUT is device) topology
    // -------------------------------------------------------------------------
    function void setup_usb_20_utmi_host_defaults();
        host_cfg.capability              = svt_usb_configuration::PLAIN;
        host_cfg.speed                   = svt_usb_types::HS;

        // Host uses TLM (internal PHY); DUT/device uses UTMI MAC interface
        host_cfg.usb_20_signal_interface = svt_usb_configuration::UTMI_IF;
        host_cfg.usb_ss_signal_interface = svt_usb_configuration::NO_SS_IF;
        host_cfg.usb_capability          = svt_usb_configuration::USB_20_ONLY;
        host_cfg.poweron_auto_attach_delay = 0;

        // UTMI data width 8-bit to match DUT
        host_cfg.utmi_data_width         = 8;

        // Remote device (DUT) configuration
        host_cfg.remote_device_cfg[0].device_address               = 0;
        host_cfg.remote_device_cfg[0].connected_bus_speed           = svt_usb_types::HS;
        host_cfg.remote_device_cfg[0].connected_hub_device_address  = 0;
        host_cfg.remote_device_cfg[0].functionality_support         = svt_usb_types::HS;
        host_cfg.remote_device_cfg[0].num_endpoints                 = num_endpoints;

        // Create endpoint configurations
        for (int ep = 0; ep < num_endpoints; ep++) begin
            host_cfg.remote_device_cfg[0].endpoint_cfg[ep] = new();
        end

        // Endpoint 0: CONTROL (mandatory)
        if (num_endpoints >= 1) begin
            host_cfg.remote_device_cfg[0].endpoint_cfg[0].ep_number       = 0;
            host_cfg.remote_device_cfg[0].endpoint_cfg[0].direction       = svt_usb_types::IN;
            host_cfg.remote_device_cfg[0].endpoint_cfg[0].ep_type         = svt_usb_types::CONTROL;
            host_cfg.remote_device_cfg[0].endpoint_cfg[0].interval        = 1;
            host_cfg.remote_device_cfg[0].endpoint_cfg[0].max_burst_size  = 0;
            host_cfg.remote_device_cfg[0].endpoint_cfg[0].max_packet_size = `SVT_USB_HS_CONTROL_MAX_PACKET_SIZE;
        end

        // Endpoint 1: BULK IN
        if (num_endpoints >= 2) begin
            host_cfg.remote_device_cfg[0].endpoint_cfg[1].ep_number       = 1;
            host_cfg.remote_device_cfg[0].endpoint_cfg[1].direction       = svt_usb_types::IN;
            host_cfg.remote_device_cfg[0].endpoint_cfg[1].ep_type         = svt_usb_types::BULK;
            host_cfg.remote_device_cfg[0].endpoint_cfg[1].interval        = 1;
            host_cfg.remote_device_cfg[0].endpoint_cfg[1].max_packet_size = `SVT_USB_HS_BULK_MAX_PACKET_SIZE;
        end

        // Use scaled-down timer values for faster simulation
        void'(host_cfg.set_timer_values(svt_usb_configuration::USB_VIP_SCALEDOWN_TIMER_VALUES));
    endfunction

endclass

`endif // CALIPTRA_SS_USB_SHARED_CFG_SV
