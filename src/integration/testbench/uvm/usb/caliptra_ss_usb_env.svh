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
// Current topology:
//   - One svt_usb_agent instance named host_agent.
//   - host_cfg configures the local USB 2.0 host stack.
//   - remote_cfg is cloned from dev_cfg and configures the modeled device PHY.
//   - One svt_usb_if instance carries the UTMI+ connection between remote_cfg's
//     device PHY model and the Caliptra SS USB device DUT.
// =============================================================================
class caliptra_ss_usb_env extends uvm_env;

    typedef virtual svt_usb_if USB_IF;

    `uvm_component_utils(caliptra_ss_usb_env)

    // Single virtual interface for the DUT UTMI+ connection.
    USB_IF usb_20_mac_if;

    // Single VIP agent. remote_cfg supplies the modeled device PHY.
    svt_usb_agent host_agent;

    // Configuration
    caliptra_ss_usb_shared_cfg cfg;

    // Sequence item report (system-level)
    svt_sequence_item_report seq_item_report;

    // System virtual sequencer handle used to connect to lower level agent virtual sequencer.
    svt_usb_system_virtual_sequencer sys_virt_sequencer;

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

    // Retrieve the VIP interface from config_db.
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

    /**
     * Double check that the configuration is valid before moving on
     */
    if (this.cfg.is_valid(0)) begin
      `uvm_info("build_phase", $psprintf("cfg passed is_valid() check. Contents:\n%0s", this.cfg.sprint()), UVM_HIGH)
    end else begin
      `uvm_fatal("build_phase", "cfg failed is_valid() check. Unable to continue.")
    end

    // ---------- Pass agent configurations ----------
    uvm_config_db#(svt_usb_agent_configuration)::set(this, "host_agent", "cfg", cfg.host_cfg);

    // ---------- Route VIP interfaces to agents ----------
    // The host agent consumes this interface for the remote_cfg UTMI PHY.
    if (usb_20_mac_if != null) begin
        uvm_config_db#(USB_IF)::set(this, "host_agent", "usb_20_if", usb_20_mac_if);
    end else begin
        `uvm_warning("build_phase",
            "usb_20_mac_if is null - host_agent will have no UTMI vif.")
    end

    // ---------- Create remote_cfg via canonical clone-of-dev_cfg pattern ----
    // Clone dev_cfg into remote_cfg and override component_subtype = PHY so the
    // host agent models the device-side UTMI PHY without creating a second
    // agent. The clone inherits UTMI, speed, and endpoint settings from dev_cfg.
    if (!$cast(remote_cfg, cfg.dev_cfg.clone())) begin
        `uvm_fatal("build_phase",
            "Unable to clone dev_cfg into remote_cfg")
    end
    remote_cfg.component_subtype = svt_usb_configuration::PHY;
    uvm_config_db#(svt_usb_configuration)::set(this, "host_agent",
        "remote_cfg", remote_cfg);

    /**
     * Double check that the remote configuration is valid before moving on
     */
    if (remote_cfg == null) begin
        `uvm_fatal("build_phase", "remote_cfg is null. Unable to continue.")
    end else if (!remote_cfg.is_valid(0)) begin
        `uvm_fatal("build_phase", "remote_cfg failed is_valid() check. Unable to continue.")
    end else begin
        `uvm_info("build_phase", $psprintf("remote_cfg passed is_valid() check. Contents:\n%0s", remote_cfg.sprint()), UVM_HIGH)
    end

    // ---------- System-level sequence-item report ----------
    seq_item_report = new("seq_item_report");
    uvm_config_db#(svt_sequence_item_report)::set(this, "host_agent",
        "sys_seq_item_report", seq_item_report);

    // ---------- Construct agents ----------
    host_agent = svt_usb_agent::type_id::create("host_agent", this);

    /**
     * Create the system virtual sequencer.
     */
    this.sys_virt_sequencer = svt_usb_system_virtual_sequencer::type_id::create("sys_virt_sequencer", this);

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
endfunction

// -----------------------------------------------------------------------------
function void caliptra_ss_usb_env::connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...", UVM_LOW)
    super.connect_phase(phase);

    /**
     * Connect up the host virtual sequencer.
     */
    this.sys_virt_sequencer.host_virt_sequencer = host_agent.virt_sequencer;

    `uvm_info("connect_phase", "Exiting...", UVM_LOW)
endfunction

`endif // CALIPTRA_SS_USB_ENV_SV
