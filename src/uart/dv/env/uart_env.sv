// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_env extends dv_base_env #(
    .CFG_T              (uart_env_cfg),
    .COV_T              (uart_env_cov),
    .VIRTUAL_SEQUENCER_T(uart_virtual_sequencer),
    .SCOREBOARD_T       (uart_scoreboard)
  );
  `uvm_component_utils(uart_env)

  uart_agent     m_uart_agent;
  axi_mgr_agent  m_axi_agent;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    m_axi_agent = axi_mgr_agent::type_id::create("m_axi_agent", this);
    uvm_config_db#(axi_agent_cfg)::set(this, "m_axi_agent*", "cfg", cfg.m_axi_agent_cfg);

    m_uart_agent = uart_agent::type_id::create("m_uart_agent", this);
    uvm_config_db#(uart_agent_cfg)::set(this, "m_uart_agent*", "cfg", cfg.m_uart_agent_cfg);
    cfg.m_uart_agent_cfg.en_cov = cfg.en_cov;
    void'(uvm_config_db#(intr_vif)::get(this, "", "intr_vif", cfg.intr_vif));
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.is_active) begin
      cfg.ral.default_map.set_sequencer(m_axi_agent.get_register_layering_sequencer(),
                                        m_axi_agent.get_layered_reg_adapter());
    end
    if (cfg.en_scb) begin
      m_uart_agent.monitor.tx_analysis_port.connect(scoreboard.uart_tx_fifo.analysis_export);
      m_uart_agent.monitor.rx_analysis_port.connect(scoreboard.uart_rx_fifo.analysis_export);
    end
    if (cfg.is_active && cfg.m_uart_agent_cfg.is_active) begin
      virtual_sequencer.uart_sequencer_h = m_uart_agent.sequencer;
    end
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    if (cfg.is_active) begin
      fork
        m_axi_agent.run_layered_register_vseq();
      join_none
    end
  endtask

  task run_layered_register_vseq();
    m_axi_agent.run_layered_register_vseq();
  endtask

endclass
