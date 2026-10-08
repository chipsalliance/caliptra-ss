// Copyright 2026 Google LLC  (chipsalliance project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An AXI Subordinate (Device) agent supporting active driving and passive monitoring.

class axi_sub_agent extends uvm_agent;
  `uvm_component_utils(axi_sub_agent)

  local axi_agent_cfg m_cfg;

  // Reset monitors
  local axi_reset_monitor_aw m_reset_monitor_aw;
  local axi_reset_monitor_w  m_reset_monitor_w;
  local axi_reset_monitor_b  m_reset_monitor_b;
  local axi_reset_monitor_ar m_reset_monitor_ar;
  local axi_reset_monitor_r  m_reset_monitor_r;

  // Transaction & coverage monitors
  local axi_monitor_aw m_monitor_aw;
  local axi_monitor_w  m_monitor_w;
  local axi_monitor_b  m_monitor_b;
  local axi_monitor_ar m_monitor_ar;
  local axi_monitor_r  m_monitor_r;

  // Subordinate drivers and sequencers
  local axi_sub_write_request_driver  m_write_request_driver;
  local sub_write_request_sequencer_t m_write_request_sequencer;

  local axi_sub_write_data_driver     m_write_data_driver;
  local sub_write_data_sequencer_t    m_write_data_sequencer;

  local axi_sub_write_response_driver  m_write_response_driver;
  local sub_write_response_sequencer_t m_write_response_sequencer;

  local axi_sub_read_request_driver   m_read_request_driver;
  local sub_read_request_sequencer_t  m_read_request_sequencer;

  local axi_sub_read_data_driver      m_read_data_driver;
  local sub_read_data_sequencer_t     m_read_data_sequencer;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void set_cfg(axi_agent_cfg cfg);
    if (m_cfg != null) `uvm_fatal(get_full_name(), "Cannot set cfg: m_cfg is already non-null.")
    m_cfg = cfg;
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (m_cfg == null && !uvm_config_db#(axi_agent_cfg)::get(this, "", "cfg", m_cfg)) begin
      `uvm_fatal(get_full_name(), "failed to get cfg object from uvm_config_db")
    end

    m_reset_monitor_aw = axi_reset_monitor_aw::type_id::create("m_reset_monitor_aw", this);
    m_reset_monitor_w  = axi_reset_monitor_w::type_id::create("m_reset_monitor_w", this);
    m_reset_monitor_b  = axi_reset_monitor_b::type_id::create("m_reset_monitor_b", this);
    m_reset_monitor_ar = axi_reset_monitor_ar::type_id::create("m_reset_monitor_ar", this);
    m_reset_monitor_r  = axi_reset_monitor_r::type_id::create("m_reset_monitor_r", this);

    m_monitor_aw = axi_monitor_aw::type_id::create("m_monitor_aw", this);
    m_monitor_w  = axi_monitor_w::type_id::create("m_monitor_w", this);
    m_monitor_b  = axi_monitor_b::type_id::create("m_monitor_b", this);
    m_monitor_ar = axi_monitor_ar::type_id::create("m_monitor_ar", this);
    m_monitor_r  = axi_monitor_r::type_id::create("m_monitor_r", this);

    if (get_is_active() == UVM_ACTIVE) begin
      m_write_request_driver    = axi_sub_write_request_driver::type_id::create("m_write_request_driver", this);
      m_write_request_sequencer = sub_write_request_sequencer_t::type_id::create("m_write_request_sequencer", this);

      m_write_data_driver       = axi_sub_write_data_driver::type_id::create("m_write_data_driver", this);
      m_write_data_sequencer    = sub_write_data_sequencer_t::type_id::create("m_write_data_sequencer", this);

      m_write_response_driver    = axi_sub_write_response_driver::type_id::create("m_write_response_driver", this);
      m_write_response_sequencer = sub_write_response_sequencer_t::type_id::create("m_write_response_sequencer", this);

      m_read_request_driver    = axi_sub_read_request_driver::type_id::create("m_read_request_driver", this);
      m_read_request_sequencer = sub_read_request_sequencer_t::type_id::create("m_read_request_sequencer", this);

      m_read_data_driver       = axi_sub_read_data_driver::type_id::create("m_read_data_driver", this);
      m_read_data_sequencer    = sub_read_data_sequencer_t::type_id::create("m_read_data_sequencer", this);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    m_cfg.write_request_vif.set_en_assert(m_cfg.en_assert);
    m_cfg.write_data_vif.set_en_assert(m_cfg.en_assert);
    m_cfg.write_response_vif.set_en_assert(m_cfg.en_assert);
    m_cfg.read_request_vif.set_en_assert(m_cfg.en_assert);
    m_cfg.read_data_vif.set_en_assert(m_cfg.en_assert);

    m_reset_monitor_aw.set_vif(m_cfg.write_request_vif);
    m_reset_monitor_w.set_vif(m_cfg.write_data_vif);
    m_reset_monitor_b.set_vif(m_cfg.write_response_vif);
    m_reset_monitor_ar.set_vif(m_cfg.read_request_vif);
    m_reset_monitor_r.set_vif(m_cfg.read_data_vif);

    m_monitor_aw.set_vif(m_cfg.write_request_vif);
    m_monitor_aw.set_en_cov(m_cfg.en_cov);
    m_monitor_w.set_vif(m_cfg.write_data_vif);
    m_monitor_w.set_en_cov(m_cfg.en_cov);
    m_monitor_b.set_vif(m_cfg.write_response_vif);
    m_monitor_b.set_en_cov(m_cfg.en_cov);
    m_monitor_ar.set_vif(m_cfg.read_request_vif);
    m_monitor_ar.set_en_cov(m_cfg.en_cov);
    m_monitor_r.set_vif(m_cfg.read_data_vif);
    m_monitor_r.set_en_cov(m_cfg.en_cov);

    if (get_is_active() == UVM_ACTIVE) begin
      m_write_request_driver.set_vif(m_cfg.write_request_vif);
      m_write_request_driver.seq_item_port.connect(m_write_request_sequencer.seq_item_export);

      m_write_data_driver.set_vif(m_cfg.write_data_vif);
      m_write_data_driver.seq_item_port.connect(m_write_data_sequencer.seq_item_export);

      m_write_response_driver.set_vif(m_cfg.write_response_vif);
      m_write_response_driver.seq_item_port.connect(m_write_response_sequencer.seq_item_export);

      m_read_request_driver.set_vif(m_cfg.read_request_vif);
      m_read_request_driver.seq_item_port.connect(m_read_request_sequencer.seq_item_export);

      m_read_data_driver.set_vif(m_cfg.read_data_vif);
      m_read_data_driver.seq_item_port.connect(m_read_data_sequencer.seq_item_export);
    end
  endfunction

  function axi_monitor_aw get_write_request_monitor(); return m_monitor_aw; endfunction
  function axi_monitor_w  get_write_data_monitor();    return m_monitor_w;  endfunction
  function axi_monitor_b  get_write_response_monitor();return m_monitor_b;  endfunction
  function axi_monitor_ar get_read_request_monitor();  return m_monitor_ar; endfunction
  function axi_monitor_r  get_read_data_monitor();     return m_monitor_r;  endfunction

  function sub_write_request_sequencer_t  get_write_request_sequencer();  return m_write_request_sequencer;  endfunction
  function sub_write_data_sequencer_t     get_write_data_sequencer();     return m_write_data_sequencer;     endfunction
  function sub_write_response_sequencer_t get_write_response_sequencer(); return m_write_response_sequencer; endfunction
  function sub_read_request_sequencer_t   get_read_request_sequencer();   return m_read_request_sequencer;   endfunction
  function sub_read_data_sequencer_t      get_read_data_sequencer();      return m_read_data_sequencer;      endfunction
endclass
