// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_env_cfg extends dv_base_env_cfg #(.RAL_T(uart_reg_block));
  intr_vif intr_vif;

  // ext component cfgs
  rand uart_agent_cfg   m_uart_agent_cfg;
  rand axi_agent_cfg    m_axi_agent_cfg;

  uint num_interrupts;

  // during break error, DUT will trigger additional frame/parity errors, which mon doesn't catch
  // disable parity/frame check in this period
  bit  disable_scb_rx_parity_check;
  bit  disable_scb_rx_frame_check;

  `uvm_object_utils_begin(uart_env_cfg)
    `uvm_field_object(m_uart_agent_cfg, UVM_DEFAULT)
    `uvm_field_object(m_axi_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize();
    ral_type_name = "uart_reg_block";
    initialize_ral(32, 32, 4);
    ral.set_base_addr(32'h0);
    ral.default_map.set_base_addr(32'h0);
    ral.default_map.set_base_addr('h0);
    // create uart agent config obj
    m_uart_agent_cfg = uart_agent_cfg::type_id::create("m_uart_agent_cfg");
    m_axi_agent_cfg = axi_agent_cfg::type_id::create("m_axi_agent_cfg");
    // set num_interrupts
    num_interrupts = ral.intr_state.get_n_used_bits();

    void'(uvm_config_db#(virtual axi_write_request_if)::get(null, "*", "write_request_vif", m_axi_agent_cfg.write_request_vif));
    void'(uvm_config_db#(virtual axi_write_data_if)::get(null, "*", "write_data_vif", m_axi_agent_cfg.write_data_vif));
    void'(uvm_config_db#(virtual axi_write_response_if)::get(null, "*", "write_response_vif", m_axi_agent_cfg.write_response_vif));
    void'(uvm_config_db#(virtual axi_read_request_if)::get(null, "*", "read_request_vif", m_axi_agent_cfg.read_request_vif));
    void'(uvm_config_db#(virtual axi_read_data_if)::get(null, "*", "read_data_vif", m_axi_agent_cfg.read_data_vif));
  endfunction

  // uart doesn't have reset pin. When reset occurs/clears,
  // need to call reset function in uart_agent_cfg
  virtual function void reset_asserted();
    super.reset_asserted();
    m_uart_agent_cfg.reset_asserted();
  endfunction

  virtual function void reset_deasserted();
    super.reset_deasserted();
    m_uart_agent_cfg.reset_deasserted();
  endfunction
endclass
