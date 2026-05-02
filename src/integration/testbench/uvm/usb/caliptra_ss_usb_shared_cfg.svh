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
// Single-agent topology per usb_vip_topology_reference.md:
//   - One svt_usb_agent (host_agent) with:
//     - Main cfg: component_type=HOST, usb_20_signal_interface=USB_20_TLM
//       (local Host stack — Protocol, Link, Physical — all internal/TLM)
//     - remote_cfg: component_type=DEVICE, component_subtype=PHY,
//       usb_20_signal_interface=UTMI_IF (remote Device PHY facing DUT MAC)
//   - The agent internally bridges local↔remote via TLM; remote PHY drives
//     real UTMI signals to the DUT device controller.
//   - No second agent is needed.
//
// EP descriptors are populated on host_cfg.remote_device_cfg[0] so the host
// protocol layer knows the DUT device's endpoint layout.
// =============================================================================
class caliptra_ss_usb_shared_cfg extends uvm_object;

    real timeout = `CALIPTRA_SS_USB_CFG_TIMEOUT;

    // Single agent configuration (VIP acts as host with remote device PHY)
    svt_usb_agent_configuration host_cfg;

    // Number of endpoints to configure on the device (DUT)
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
        host_cfg.local_host_cfg        = new();

        // Host's view of the remote device (DUT) — EP descriptors go here
        host_cfg.remote_device_cfg_size = 1;
        host_cfg.remote_device_cfg[0]   = new();

        // No local device cfg on the host agent
        host_cfg.local_device_cfg_size = 0;
    endfunction

    // -------------------------------------------------------------------------
    // Setup USB 2.0 HS UTMI defaults for single-agent topology.
    //
    // The host_cfg is the agent's main (local) configuration with USB_20_TLM.
    // The env will create a separate remote_cfg object with UTMI_IF + DEVICE +
    // PHY and push it via config_db. EP descriptors are set here on
    // host_cfg.remote_device_cfg[0].
    // -------------------------------------------------------------------------
    function void setup_usb_20_utmi_host_defaults();
        // ---------------- host agent main cfg (local Host stack, TLM) --------
        host_cfg.capability                = svt_usb_configuration::PLAIN;
        host_cfg.speed                     = svt_usb_types::HS;
        host_cfg.usb_20_signal_interface   = svt_usb_configuration::USB_20_TLM;
        host_cfg.usb_ss_signal_interface   = svt_usb_configuration::NO_SS_IF;
        host_cfg.usb_capability            = svt_usb_configuration::USB_20_ONLY;
        host_cfg.utmi_data_width           = 8;
        host_cfg.poweron_auto_attach_delay = 0;

        // ---------------- Remote device descriptor (DUT's EP layout) --------
        host_cfg.remote_device_cfg[0].device_address              = 0;
        host_cfg.remote_device_cfg[0].connected_bus_speed         = svt_usb_types::HS;
        host_cfg.remote_device_cfg[0].connected_hub_device_address = 0;
        host_cfg.remote_device_cfg[0].functionality_support       = svt_usb_types::HS;
        host_cfg.remote_device_cfg[0].num_endpoints               = num_endpoints;

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

        // Scaled-down timers for faster simulation
        void'(host_cfg.set_timer_values(svt_usb_configuration::USB_VIP_SCALEDOWN_TIMER_VALUES));
    endfunction

endclass

`endif // CALIPTRA_SS_USB_SHARED_CFG_SV
