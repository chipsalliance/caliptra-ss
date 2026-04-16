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

`ifndef GUARD_CALIPTRA_SS_USB_ENV_SV
`define GUARD_CALIPTRA_SS_USB_ENV_SV

`include "caliptra_ss_usb_shared_cfg.sv"

// =============================================================================
// USB VIP environment for Caliptra Subsystem testbench.
//
// This environment instantiates a single VIP host agent. The DUT
// (caliptra_ss_top) acts as the USB device — there is no VIP device agent.
// The host agent connects to the DUT via the UTMI MAC-side interface.
// =============================================================================
class caliptra_ss_usb_env extends uvm_env;

    typedef virtual svt_usb_if USB_IF;

    `uvm_component_utils(caliptra_ss_usb_env)

    // Virtual interface handle for the UTMI MAC-side connection
    USB_IF usb_20_mac_if;

    // VIP host agent
    svt_usb_agent host_agent;

    // Configuration
    caliptra_ss_usb_shared_cfg cfg;

    // Sequence item report
    svt_sequence_item_report seq_item_report;

    function new(string name = "caliptra_ss_usb_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    extern virtual function void build_phase(uvm_phase phase);
    extern virtual function void connect_phase(uvm_phase phase);

endclass

// -----------------------------------------------------------------------------
function void caliptra_ss_usb_env::build_phase(uvm_phase phase);
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

    // Pass host agent configuration
    uvm_config_db#(svt_usb_agent_configuration)::set(this, "host_agent", "cfg", cfg.host_cfg);

    // Pass the VIP interface to the host agent as a USB 2.0 interface
    if (usb_20_mac_if != null) begin
        uvm_config_db#(USB_IF)::set(this, "host_agent", "usb_20_if", usb_20_mac_if);
    end else begin
        `uvm_warning("build_phase", "usb_20_mac_if is null — host agent will have no interface connection.")
    end

    // Create sequence item report
    seq_item_report = new("seq_item_report");
    uvm_config_db#(svt_sequence_item_report)::set(this, "host_agent",
        "sys_seq_item_report", seq_item_report);

    // Construct host agent
    host_agent = svt_usb_agent::type_id::create("host_agent", this);

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
endfunction

// -----------------------------------------------------------------------------
function void caliptra_ss_usb_env::connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...", UVM_LOW)
    super.connect_phase(phase);
    `uvm_info("connect_phase", "Exiting...", UVM_LOW)
endfunction

`endif // GUARD_CALIPTRA_SS_USB_ENV_SV
