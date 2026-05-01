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
// Two-agent topology matching the canonical
// tb_usb_svt_uvm_basic_sys/host_phy_device_mac example:
//   - host_agent: component_type=HOST,   usb_20_signal_interface=USB_20_TLM
//                 (no on-wire interface; runs over the VIP TLM-internal PHY)
//   - dev_agent:  component_type=DEVICE, usb_20_signal_interface=UTMI_IF
//                 (owns the svt_usb_if vif on the DUT MAC side)
//
// EP descriptors are populated only on dev_cfg.local_device_cfg[0]; the host's
// remote_device_cfg array is pointer-aliased to dev_cfg.local_device_cfg so
// both agents share the same EP table.
// =============================================================================
class caliptra_ss_usb_shared_cfg extends uvm_object;

    real timeout = `CALIPTRA_SS_USB_CFG_TIMEOUT;

    // Host agent configuration (VIP acts as host)
    svt_usb_agent_configuration host_cfg;
    // Device agent configuration (VIP emulates dev PHY)
    svt_usb_agent_configuration dev_cfg;

    // Number of endpoints to configure on the device (DUT)
    int num_endpoints = 2;

    `uvm_object_utils_begin(caliptra_ss_usb_shared_cfg)
        `uvm_field_object(host_cfg, UVM_ALL_ON|UVM_DEEP)
        `uvm_field_object(dev_cfg,  UVM_ALL_ON|UVM_DEEP)
        `uvm_field_real  (timeout,  UVM_ALL_ON)
        `uvm_field_int   (num_endpoints, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name = "caliptra_ss_usb_shared_cfg");
        super.new(name);

        host_cfg = new();
        host_cfg.component_type = svt_usb_types::HOST;
        host_cfg.top_layer      = svt_usb_agent_configuration::PROTOCOL;
        host_cfg.local_host_cfg        = new();
        host_cfg.local_device_cfg_size = 0;

        dev_cfg = new();
        dev_cfg.component_type = svt_usb_types::DEVICE;
        dev_cfg.top_layer      = svt_usb_agent_configuration::PROTOCOL;
        dev_cfg.local_host_cfg         = null;
        dev_cfg.local_device_cfg_size  = 1;
        dev_cfg.local_device_cfg[0]    = new();

        // Cross-link: host's view of the remote device == device's local cfg
        // (pointer alias — same handle, so EP table stays in sync).
        host_cfg.remote_device_cfg_size = dev_cfg.local_device_cfg_size;
        host_cfg.remote_device_cfg      = dev_cfg.local_device_cfg;
        host_cfg.remote_host_cfg        = dev_cfg.local_host_cfg;

        dev_cfg.remote_host_cfg         = host_cfg.local_host_cfg;
        dev_cfg.remote_device_cfg_size  = host_cfg.local_device_cfg_size;
    endfunction

    // -------------------------------------------------------------------------
    // Setup USB 2.0 HS UTMI defaults for two-agent (host TLM + dev UTMI) topology
    // -------------------------------------------------------------------------
    function void setup_usb_20_utmi_host_defaults();
        // ---------------- host_agent (TLM) ----------------
        host_cfg.capability                = svt_usb_configuration::PLAIN;
        host_cfg.speed                     = svt_usb_types::HS;
        host_cfg.usb_20_signal_interface   = svt_usb_configuration::USB_20_TLM;
        host_cfg.usb_ss_signal_interface   = svt_usb_configuration::NO_SS_IF;
        host_cfg.usb_capability            = svt_usb_configuration::USB_20_ONLY;
        host_cfg.poweron_auto_attach_delay = 0;

        // ---------------- dev_agent (UTMI MAC-side) ----------------
        dev_cfg.capability                 = svt_usb_configuration::PLAIN;
        dev_cfg.speed                      = svt_usb_types::HS;
        dev_cfg.usb_20_signal_interface    = svt_usb_configuration::UTMI_IF;
        dev_cfg.usb_ss_signal_interface    = svt_usb_configuration::NO_SS_IF;
        dev_cfg.usb_capability             = svt_usb_configuration::USB_20_ONLY;
        dev_cfg.utmi_data_width            = 8;
        dev_cfg.poweron_auto_attach_delay  = 0;

        // ---------------- Device function descriptor (shared via alias) ----------------
        dev_cfg.local_device_cfg[0].device_address              = 0;
        dev_cfg.local_device_cfg[0].connected_bus_speed         = svt_usb_types::HS;
        dev_cfg.local_device_cfg[0].connected_hub_device_address = 0;
        dev_cfg.local_device_cfg[0].functionality_support       = svt_usb_types::HS;
        dev_cfg.local_device_cfg[0].num_endpoints               = num_endpoints;

        for (int ep = 0; ep < num_endpoints; ep++) begin
            dev_cfg.local_device_cfg[0].endpoint_cfg[ep] = new();
        end

        // Endpoint 0: CONTROL (mandatory)
        if (num_endpoints >= 1) begin
            dev_cfg.local_device_cfg[0].endpoint_cfg[0].ep_number       = 0;
            dev_cfg.local_device_cfg[0].endpoint_cfg[0].direction       = svt_usb_types::IN;
            dev_cfg.local_device_cfg[0].endpoint_cfg[0].ep_type         = svt_usb_types::CONTROL;
            dev_cfg.local_device_cfg[0].endpoint_cfg[0].interval        = 1;
            dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_burst_size  = 0;
            dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size = `SVT_USB_HS_CONTROL_MAX_PACKET_SIZE;
        end

        // Endpoint 1: BULK IN
        if (num_endpoints >= 2) begin
            dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number       = 1;
            dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction       = svt_usb_types::IN;
            dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type         = svt_usb_types::BULK;
            dev_cfg.local_device_cfg[0].endpoint_cfg[1].interval        = 1;
            dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size = `SVT_USB_HS_BULK_MAX_PACKET_SIZE;
        end

        // Scaled-down timers on both cfgs for faster simulation
        void'(host_cfg.set_timer_values(svt_usb_configuration::USB_VIP_SCALEDOWN_TIMER_VALUES));
        void'(dev_cfg.set_timer_values (svt_usb_configuration::USB_VIP_SCALEDOWN_TIMER_VALUES));
    endfunction

endclass

`endif // CALIPTRA_SS_USB_SHARED_CFG_SV
