// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// you may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// UVM environment for the compound USB unitbench.
// Connects four direct Avery AXI managers to an access-only generated RAL model;
// no interconnect, register predictor, or scoreboard is added here.
// Creates the Synopsys USB host and remote UTMI PHY configuration for live USB
// stimulus. Virtual interfaces come from usb_top_tb.

// Own the manager ports, RAL routing, USB agent, shared sequence context, and
// reset-access gate.
class usb_env extends uvm_env;
  `uvm_component_utils(usb_env)

  // -----------------------------------------------------------------------------
  // Components and configuration
  // -----------------------------------------------------------------------------

  typedef virtual svt_usb_if usb_vif_t;

  // One manager per DUT port: DEV0 CSR/HUB, DEV0 SRAM, DEV1 CSR, and DEV1 SRAM.
  aaxi_agent combo_manager;
  aaxi_agent dev0_memory_manager;
  aaxi_agent dev1_csr_manager;
  aaxi_agent dev1_memory_manager;

  aaxi_vip_config combo_config;
  aaxi_vip_config dev0_memory_config;
  aaxi_vip_config dev1_csr_config;
  aaxi_vip_config dev1_memory_config;

  usb_env_cfg cfg;
  usb_vif_t usb_20_mac_if;
  svt_usb_agent host_agent;
  svt_sequence_item_report usb_sequence_item_report;
  usb_virtual_sequencer virtual_sequencer;

  // Each root RAL map has its own adapter; identical local addresses are legal.
  usb_reg_model reg_model;
  usb_axi_reg_adapter combo_adapter;
  usb_axi_reg_adapter dev0_memory_adapter;
  usb_axi_reg_adapter dev1_csr_adapter;
  usb_axi_reg_adapter dev1_memory_adapter;

  // -----------------------------------------------------------------------------
  // Construction and AXI manager helpers
  // -----------------------------------------------------------------------------

  // Register this environment under its parent; create children in build_phase.
  function new(string name = "usb_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  // Enable all five USER channels with the widths used by the bench interfaces.
  // Set before agent construction: zero transaction values alone do not enable
  // Avery's request USER signals.
  function void configure_user_channels(aaxi_vip_config manager_config);
    manager_config.set_config_int("opt_awuser_enable", 1);
    manager_config.set_config_int("opt_wuser_enable", 1);
    manager_config.set_config_int("opt_buser_enable", 1);
    manager_config.set_config_int("opt_aruser_enable", 1);
    manager_config.set_config_int("opt_ruser_enable", 1);
    manager_config.set_config_int("awuser_width", USB_TB_AXI_USER_WIDTH);
    manager_config.set_config_int("wuser_width", USB_TB_AXI_USER_WIDTH);
    manager_config.set_config_int("buser_width", USB_TB_AXI_USER_WIDTH);
    manager_config.set_config_int("aruser_width", USB_TB_AXI_USER_WIDTH);
    manager_config.set_config_int("ruser_width", USB_TB_AXI_USER_WIDTH);
  endfunction

  // Bind a named top-level VIF and prepare one active AXI4 manager configuration.
  // Missing/null interfaces are fatal rather than leaving a disconnected agent.
  function aaxi_vip_config create_manager_config(string manager_name, string vif_field_name);
    aaxi_vip_config manager_config;

    manager_config = aaxi_vip_config::type_id::create({manager_name, "_config"});
    if (!uvm_config_db#(virtual aaxi_intf)::get(this, "", vif_field_name, manager_config.vif)) begin
      `uvm_fatal("USB_ENV", $sformatf("Missing Avery VIF for %s", manager_name))
    end
    if (manager_config.vif == null) begin
      `uvm_fatal("USB_ENV", $sformatf("Null Avery VIF for %s", manager_name))
    end

    manager_config.set_config_int("agent_type", AAXI_MASTER);
    manager_config.set_config_int("is_active", 1);
    manager_config.set_config_int("version", AAXI4);
    manager_config.set_config_int("data_bus_bytes", USB_AXI_DATA_WIDTH / 8);
    manager_config.set_config_int("id_width", AAXI_ID_WIDTH);
    manager_config.set_config_int("addr_width", AAXI_ADDR_WIDTH);
    // Keep each manager single-outstanding; sequences provide data comparisons.
    manager_config.set_config_int("total_outstanding_depth", 1);
    manager_config.set_config_int("id_outstanding_depth", 1);
    manager_config.set_config_int("enable_scoreboard", 0);
    configure_user_channels(manager_config);
    return manager_config;
  endfunction

  // Create a native Avery child agent and install its prepared port settings.
  function aaxi_agent create_manager_agent(string instance_name, aaxi_vip_config manager_config);
    aaxi_agent manager_agent;

    manager_agent = aaxi_agent::type_id::create(instance_name, this);
    manager_agent.set_config(manager_config);
    `uvm_info("USB_ENV", $sformatf("%s configured: AXI4 data=32 ID=%0d USER=%0d outstanding=1", instance_name, AAXI_ID_WIDTH, USB_TB_AXI_USER_WIDTH), UVM_LOW)
    return manager_agent;
  endfunction

  // -----------------------------------------------------------------------------
  // UVM build phase
  // -----------------------------------------------------------------------------

  // Construct AXI/RAL infrastructure and publish the USB configuration before
  // creating the host child that consumes it.
  function void build_phase(uvm_phase phase);
    svt_usb_configuration remote_cfg;

    super.build_phase(phase);

    // ---------------------------------------------------------------------------
    // AXI manager setup
    // ---------------------------------------------------------------------------

    virtual_sequencer  = usb_virtual_sequencer::type_id::create("virtual_sequencer", this);
    cfg                = usb_env_cfg::type_id::create("cfg");
    combo_config       = create_manager_config("combo", "combo_vif");
    dev0_memory_config = create_manager_config("dev0_memory", "dev0_memory_vif");
    dev1_csr_config    = create_manager_config("dev1_csr", "dev1_csr_vif");
    dev1_memory_config = create_manager_config("dev1_memory", "dev1_memory_vif");

    combo_manager       = create_manager_agent("combo_manager", combo_config);
    dev0_memory_manager = create_manager_agent("dev0_memory_manager", dev0_memory_config);
    dev1_csr_manager    = create_manager_agent("dev1_csr_manager", dev1_csr_config);
    dev1_memory_manager = create_manager_agent("dev1_memory_manager", dev1_memory_config);

    // ---------------------------------------------------------------------------
    // RAL model and adapter setup
    // ---------------------------------------------------------------------------

    // Finalize the map hierarchy before validating physical SRAM row addresses.
    // The resulting model provides accesses, not automatic expected-value checks.
    reg_model = usb_reg_model::type_id::create("reg_model");
    reg_model.configure(null);
    reg_model.build();
    reg_model.lock_model();
    reg_model.validate_packet_memory_maps();
    reg_model.configure_access_only();

    // Fixed IDs identify the four manager paths consistently with native traffic.
    combo_adapter       = usb_axi_reg_adapter::type_id::create("combo_adapter");
    dev0_memory_adapter = usb_axi_reg_adapter::type_id::create("dev0_memory_adapter");
    dev1_csr_adapter    = usb_axi_reg_adapter::type_id::create("dev1_csr_adapter");
    dev1_memory_adapter = usb_axi_reg_adapter::type_id::create("dev1_memory_adapter");

    combo_adapter.transaction_id       = aaxi_id_t'(1);
    dev0_memory_adapter.transaction_id = aaxi_id_t'(2);
    dev1_csr_adapter.transaction_id    = aaxi_id_t'(3);
    dev1_memory_adapter.transaction_id = aaxi_id_t'(4);

    // ---------------------------------------------------------------------------
    // USB VIP setup
    // ---------------------------------------------------------------------------

    `uvm_info("USB_ENV", "Configuring Synopsys SVT USB host agent and remote UTMI device PHY", UVM_LOW)
    if (!uvm_config_db#(usb_vif_t)::get(this, "", "usb_20_mac_if", usb_20_mac_if) || usb_20_mac_if == null) begin
      `uvm_fatal("USB_ENV", "Missing usb_20_mac_if for SVT USB INIT")
    end

    // Prepare both peers before exposing configuration to the host agent.
    cfg.configure_usb_vip();
    cfg.validate_usb_vip();
    uvm_config_db#(svt_usb_agent_configuration)::set(this, "host_agent", "cfg", cfg.host_cfg);
    uvm_config_db#(usb_vif_t)::set(this, "host_agent", "usb_20_if", usb_20_mac_if);
    uvm_config_db#(usb_vif_t)::set(this, "host_agent", "usb_20_mac_if", usb_20_mac_if);

    // Derive a PHY-only remote configuration without modifying cfg's template.
    // The DUT supplies the device controller; no separate device agent is built.
    if (!$cast(remote_cfg, cfg.device_phy_cfg.clone())) begin
      `uvm_fatal("USB_ENV", "Unable to clone USB device PHY configuration")
    end
    remote_cfg.component_subtype = svt_usb_configuration::PHY;
    if (!remote_cfg.is_valid(0)) begin
      `uvm_fatal("USB_ENV", "USB remote PHY configuration is invalid")
    end
    uvm_config_db#(svt_usb_configuration)::set(this, "host_agent", "remote_cfg", remote_cfg);

    // Give the host a report object for its system-sequence items.
    usb_sequence_item_report = new("usb_sequence_item_report");
    uvm_config_db#(svt_sequence_item_report)::set(this, "host_agent", "sys_seq_item_report", usb_sequence_item_report);
    host_agent = svt_usb_agent::type_id::create("host_agent", this);
  endfunction

  // -----------------------------------------------------------------------------
  // UVM connect phase
  // -----------------------------------------------------------------------------

  // Route each RAL map through the matching adapter and Avery manager sequencer.
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    // ---------------------------------------------------------------------------
    // Virtual sequencer wiring
    // ---------------------------------------------------------------------------

    if (virtual_sequencer == null ||
        reg_model == null ||
        combo_manager == null ||
        combo_manager.sequencer == null ||
        dev0_memory_manager == null ||
        dev0_memory_manager.sequencer == null ||
        dev1_csr_manager == null ||
        dev1_csr_manager.sequencer == null ||
        dev1_memory_manager == null ||
        dev1_memory_manager.sequencer == null ||
        host_agent == null ||
        host_agent.virt_sequencer == null) begin
      `uvm_fatal("USB_ENV", "Virtual sequencer dependencies are not fully constructed")
    end
    virtual_sequencer.reg_model = reg_model;
    virtual_sequencer.combo_sequencer = combo_manager.sequencer;
    virtual_sequencer.dev0_memory_sequencer = dev0_memory_manager.sequencer;
    virtual_sequencer.dev1_csr_sequencer = dev1_csr_manager.sequencer;
    virtual_sequencer.dev1_memory_sequencer = dev1_memory_manager.sequencer;
    virtual_sequencer.host_sequencer = host_agent.virt_sequencer;

    // ---------------------------------------------------------------------------
    // Adapter-to-sequencer wiring
    // ---------------------------------------------------------------------------

    // Adapters need the sequencer handle to copy the correct manager parameters.
    combo_adapter.manager_sequencer       = combo_manager.sequencer;
    dev0_memory_adapter.manager_sequencer = dev0_memory_manager.sequencer;
    dev1_csr_adapter.manager_sequencer    = dev1_csr_manager.sequencer;
    dev1_memory_adapter.manager_sequencer = dev1_memory_manager.sequencer;

    // ---------------------------------------------------------------------------
    // RAL map bindings
    // ---------------------------------------------------------------------------

    // Map bindings select the physical port when a sequence requests RAL access.
    reg_model.combo_map.set_sequencer(combo_manager.sequencer, combo_adapter);
    reg_model.dev0_mem_map.set_sequencer(dev0_memory_manager.sequencer, dev0_memory_adapter);
    reg_model.dev1_csr_map.set_sequencer(dev1_csr_manager.sequencer, dev1_csr_adapter);
    reg_model.dev1_mem_map.set_sequencer(dev1_memory_manager.sequencer, dev1_memory_adapter);
    `uvm_info("USB_ENV", "Bound four access-only RAL maps to their Avery manager sequencers", UVM_LOW)
  endfunction

  // -----------------------------------------------------------------------------
  // Reset synchronization
  // -----------------------------------------------------------------------------

  // Bound the wait for manager reset release before endpoint accesses begin.
  // Use the combo port as the reference and require all peers released by its
  // next rising clock edge; report a mismatch or timeout as fatal.
  task wait_for_reset();
    `uvm_info("USB_ENV", "Waiting for reset release on all four managers", UVM_LOW)
    fork
      begin
        // Require a known deasserted reset, then sample the other manager resets.
        wait (combo_config.vif.ARESETn === 1'b1);
        @(posedge combo_config.vif.ACLK);
        if (dev0_memory_config.vif.ARESETn !== 1'b1 ||
            dev1_csr_config.vif.ARESETn !== 1'b1 ||
            dev1_memory_config.vif.ARESETn !== 1'b1) begin
          `uvm_fatal("USB_RESET", "Manager reset signals did not release together")
        end
      end
      begin
        #(USB_RESET_TIMEOUT);
        `uvm_fatal("USB_RESET_TIMEOUT", "Reset did not release on all four managers")
      end
    join_any
    // Cancel the remaining reset/timeout branch after either branch finishes.
    disable fork;
    `uvm_info("USB_ENV", "All four managers out of reset; endpoint accesses may start", UVM_LOW)
  endtask
endclass
