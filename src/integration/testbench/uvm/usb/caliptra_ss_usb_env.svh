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

`ifndef CALIPTRA_SS_USB_ENV_SV
`define CALIPTRA_SS_USB_ENV_SV

// =============================================================================
// USB VIP environment for Caliptra Subsystem testbench.
//
// Single-agent topology per usb_vip_topology_reference.md:
//   - host_agent: One svt_usb_agent configured as HOST (USB_20_TLM locally).
//     A remote_cfg with component_type=DEVICE, component_subtype=PHY,
//     usb_20_signal_interface=UTMI_IF creates an internal remote Device PHY
//     that drives real UTMI signals to the DUT device controller (MAC).
//   - No second agent. The DUT is the real USB device on the wire.
// =============================================================================
class caliptra_ss_usb_env extends uvm_env;

    typedef virtual svt_usb_if USB_IF;

    `uvm_component_utils(caliptra_ss_usb_env)

    // Virtual interface handle for the UTMI connection to DUT
    USB_IF usb_20_mac_if;

    // Single VIP agent (Host with remote Device PHY)
    svt_usb_agent host_agent;

    // Configuration
    caliptra_ss_usb_shared_cfg cfg;

    // Sequence item report (system-level)
    svt_sequence_item_report seq_item_report;

    function new(string name = "caliptra_ss_usb_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    extern virtual function void build_phase(uvm_phase phase);
    extern virtual function void connect_phase(uvm_phase phase);

endclass

// -----------------------------------------------------------------------------
function void caliptra_ss_usb_env::build_phase(uvm_phase phase);
    svt_usb_configuration remote_cfg;

    `uvm_info("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);

    // Retrieve the VIP interface from config_db
    void'(uvm_config_db#(virtual svt_usb_if)::get(null, get_full_name(),
          "usb_20_mac_if", usb_20_mac_if));

    // Retrieve or create configuration
    if (!uvm_config_db#(caliptra_ss_usb_shared_cfg)::get(this, "", "cfg", cfg)) begin
        `uvm_info("build_phase", "No external cfg provided, creating default.", UVM_LOW)
        cfg = caliptra_ss_usb_shared_cfg::type_id::create("cfg", this);
        cfg.setup_usb_20_utmi_host_defaults();
    end else begin
        `uvm_info("build_phase", "Using externally provided cfg.", UVM_LOW)
    end

    // ---------- Pass agent configuration ----------
    uvm_config_db#(svt_usb_agent_configuration)::set(this, "host_agent", "cfg", cfg.host_cfg);

    // ---------- Route usb_20_if to host_agent ----------
    // The agent uses this vif to bind its remote_phys_lane (Device PHY)
    // to the UTMI signals connected to the DUT.
    if (usb_20_mac_if != null) begin
        uvm_config_db#(USB_IF)::set(this, "host_agent", "usb_20_if", usb_20_mac_if);
    end else begin
        `uvm_warning("build_phase",
            "usb_20_mac_if is null - host_agent will have no UTMI vif.")
    end

    // ---------- Create remote_cfg for the Device PHY facing the DUT ----------
    // Per usb_vip_topology_reference.md:
    //   component_type          = DEVICE  (remote side is a device PHY)
    //   component_subtype       = PHY     (physical layer facing DUT MAC)
    //   usb_20_signal_interface = UTMI_IF (UTMI signal interface to DUT)
    begin
        svt_usb_agent_configuration remote_agent_cfg;
        remote_agent_cfg = new();
        remote_agent_cfg.component_type          = svt_usb_types::DEVICE;
        remote_agent_cfg.component_subtype       = svt_usb_configuration::PHY;
        remote_agent_cfg.speed                   = svt_usb_types::HS;
        remote_agent_cfg.usb_20_signal_interface = svt_usb_configuration::UTMI_IF;
        remote_agent_cfg.usb_ss_signal_interface = svt_usb_configuration::NO_SS_IF;
        remote_agent_cfg.usb_capability          = svt_usb_configuration::USB_20_ONLY;
        remote_agent_cfg.utmi_data_width         = 8;
        remote_agent_cfg.capability              = svt_usb_configuration::PLAIN;
        $cast(remote_cfg, remote_agent_cfg);
        uvm_config_db#(svt_usb_configuration)::set(this, "host_agent",
            "remote_cfg", remote_cfg);
    end

    // ---------- System-level sequence-item report ----------
    seq_item_report = new("seq_item_report");
    uvm_config_db#(svt_sequence_item_report)::set(this, "host_agent",
        "sys_seq_item_report", seq_item_report);

    // ---------- Construct agent ----------
    host_agent = svt_usb_agent::type_id::create("host_agent", this);

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
endfunction

// -----------------------------------------------------------------------------
function void caliptra_ss_usb_env::connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...", UVM_LOW)
    super.connect_phase(phase);
    // No callbacks needed — the DUT is the real device on the wire.
    `uvm_info("connect_phase", "Exiting...", UVM_LOW)
endfunction

`endif // CALIPTRA_SS_USB_ENV_SV
