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
// Two-agent topology (host_phy_device_mac):
//   - host_agent runs over USB_20_TLM (no on-wire vif).
//   - dev_agent  runs over UTMI_IF and owns the svt_usb_if vif connected
//     to the DUT's UTMI MAC-side modport (utmi_dut_mac_if).
//
// Because the dev side of the bus is exposed via the VIP's UTMI PHY-port
// (svt_usb_physical_port_utmi in PHY subtype), the host_agent is told via
// a cloned remote_cfg with component_subtype=PHY that there is a PHY
// between it and the DUT MAC. This is what makes the agent on the wire
// drive PHY-side outputs (LineState, RxValid/Active/Error/Data, TxReady,
// HostDisconnect) into the DUT.
// =============================================================================
class caliptra_ss_usb_env extends uvm_env;

    typedef virtual svt_usb_if USB_IF;

    `uvm_component_utils(caliptra_ss_usb_env)

    // Virtual interface handle for the UTMI MAC-side connection (owned by dev_agent)
    USB_IF usb_20_mac_if;

    // VIP agents
    svt_usb_agent host_agent;
    svt_usb_agent dev_agent;

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
    svt_usb_agent_configuration remote_cfg;

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

    // ---------- Pass per-agent configuration ----------
    uvm_config_db#(svt_usb_agent_configuration)::set(this, "host_agent", "cfg", cfg.host_cfg);
    uvm_config_db#(svt_usb_agent_configuration)::set(this, "dev_agent",  "cfg", cfg.dev_cfg);

    // ---------- Route vif to the agent on the wire (dev_agent on UTMI) ----------
    if (usb_20_mac_if != null) begin
        uvm_config_db#(USB_IF)::set(this, "dev_agent", "usb_20_if", usb_20_mac_if);
    end else begin
        `uvm_warning("build_phase",
            "usb_20_mac_if is null - dev_agent will have no UTMI vif.")
    end

    // ---------- Tell host_agent that its peer near-side is a PHY ----------
    // Mirrors usb_basic_inline_env.sv ~line 345-355: when the device-side cfg
    // uses UTMI, clone dev_cfg into a remote_cfg, stamp subtype=PHY, and push
    // it to host_agent. This drives the wire-side agent to use
    // svt_usb_physical_port_utmi in PHY subtype, which is what produces
    // LineState/RxValid/etc. on the bus.
    if (cfg.dev_cfg.usb_20_signal_interface == svt_usb_configuration::UTMI_IF) begin
        $cast(remote_cfg, cfg.dev_cfg.clone());
        remote_cfg.component_subtype = svt_usb_configuration::PHY;
        uvm_config_db#(svt_usb_agent_configuration)::set(this, "host_agent",
            "remote_cfg", remote_cfg);
    end

    // ---------- System-level sequence-item report on both agents ----------
    seq_item_report = new("seq_item_report");
    uvm_config_db#(svt_sequence_item_report)::set(this, "host_agent",
        "sys_seq_item_report", seq_item_report);
    uvm_config_db#(svt_sequence_item_report)::set(this, "dev_agent",
        "sys_seq_item_report", seq_item_report);

    // ---------- Construct agents ----------
    host_agent = svt_usb_agent::type_id::create("host_agent", this);
    dev_agent  = svt_usb_agent::type_id::create("dev_agent",  this);

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
endfunction

// -----------------------------------------------------------------------------
function void caliptra_ss_usb_env::connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...", UVM_LOW)
    super.connect_phase(phase);
    `uvm_info("connect_phase", "Exiting...", UVM_LOW)
endfunction

`endif // CALIPTRA_SS_USB_ENV_SV
