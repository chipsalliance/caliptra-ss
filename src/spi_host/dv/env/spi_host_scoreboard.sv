// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Forward declaration of scoreboard
typedef class spi_host_scoreboard;

class spi_host_reg_cbs extends uvm_reg_cbs;
  spi_host_scoreboard sb;

  virtual task pre_write(uvm_reg_item rw);
    sb.reg_pre_write(rw.element.get_name(), rw.value[0]);
  endtask

  virtual task post_write(uvm_reg_item rw);
    if (rw.status != UVM_IS_OK) return;
    sb.reg_write(rw.element.get_name(), rw.value[0]);
  endtask

  virtual task post_read(uvm_reg_item rw);
    if (rw.status != UVM_IS_OK) return;
    sb.reg_read(rw.element.get_name(), rw.value[0]);
  endtask
endclass

class spi_host_mem_cbs extends uvm_reg_cbs;
  spi_host_scoreboard sb;

  virtual task pre_write(uvm_reg_item rw);
    sb.mem_pre_write(rw.element.get_name());
  endtask

  virtual task post_write(uvm_reg_item rw);
    uvm_reg_byte_en_t byte_en = 4'hf;
    axi_reg_op_item   ext_item;
    if (rw.status != UVM_IS_OK) return;
    if (rw.extension != null && $cast(ext_item, rw.extension)) begin
      byte_en = ext_item.m_rw.byte_en;
    end
    sb.mem_write(rw.element.get_name(), rw.offset, rw.value[0], byte_en);
  endtask

  virtual task pre_read(uvm_reg_item rw);
    sb.mem_pre_read(rw.element.get_name());
  endtask

  virtual task post_read(uvm_reg_item rw);
    if (rw.status != UVM_IS_OK) return;
    sb.mem_read(rw.element.get_name(), rw.offset, rw.value[0]);
  endtask
endclass


class spi_host_scoreboard extends dv_base_scoreboard #(
    .RAL_T(spi_host_reg_block),
    .CFG_T(spi_host_env_cfg),
    .COV_T(spi_host_env_cov)
  );
  `uvm_component_utils(spi_host_scoreboard)
  `uvm_component_new

  virtual spi_if  spi_vif;

  // TLM fifos hold the transactions sent from monitor
  uvm_tlm_analysis_fifo #(spi_item) plain_data_fifo;

  // hold expected transactions
  spi_segment_item                  host_wr_segment;
  spi_segment_item                  host_rd_segment;
  spi_item                          plain_item;

  // local variables
  // queues hold expected read and write transactions issued by register interface
  typedef struct {
    bit [7:0] bytes[$];
  } tx_word_t;

  local spi_segment_item            staged_cmd_q[$];
  local spi_segment_item            write_segment_q[$];
  local spi_segment_item            read_segment_q[$];
  local tx_word_t                   tx_word_q[$];
  local logic [7:0]                 rx_data_q[$];
  local bit                         csaat = 0;
  local int                         spi_clk_half_period;
  local int                         cur_tx_fifo_bytes = 0;
  local bit [5:0]                   sw_error_bits = 6'b0;

  // interrupt bit vector
  local bit [NumSpiHostIntr-1:0]    intr_state = 2'b00;
  local bit [NumSpiHostIntr-1:0]    intr_enable = 2'b00;
  local bit [NumSpiHostIntr-1:0]    intr_test = 2'b00;

  // Capture DUT register contents during accesses
  local spi_host_command_t          spi_cmd_reg;
  local spi_host_ctrl_t             spi_ctrl_reg;
  local spi_host_status_t           spi_status_reg;
  local spi_host_error_enable_t     spi_error_enable_reg;
  local spi_host_error_status_t     spi_error_status_reg;
  local spi_host_event_enable_t     spi_event_enable_reg;
  local spi_host_intr_state_t       spi_intr_state_reg;
  local spi_host_intr_enable_t      spi_intr_enable_reg;
  local spi_host_intr_test_t        spi_intr_test_reg;
  spi_host_configopts_t             spi_configopts;
  spi_host_configopts_t             spi_configopts_per_cs[SPI_HOST_NUM_CS];
  spi_host_configopts_t             active_cs_configopts[SPI_HOST_NUM_CS];
  spi_host_configopts_t             pending_lead_cfg_q[SPI_HOST_NUM_CS][$];
  int unsigned                      early_csb_done_cnt[SPI_HOST_NUM_CS];
  spi_host_configopts_t             curr_spi_configopts;
  bit                               initialise_configopts[SPI_HOST_NUM_CS];
  bit                               prev_cmd_csaat = 0;
  int unsigned                      prev_cmd_csid  = 0;

  // Pre-access hardware state snapshots
  bit                               was_active_at_pre_write   = 0;
  bit                               was_cmd_busy_at_pre_write = 0;
  bit                               was_txfull_at_pre_write   = 0;
  bit                               was_rxempty_at_pre_read   = 0;

  // Tally-Counters
  int                               in_tx_seg_cnt      = 0;
  int                               checked_tx_seg_cnt = 0;
  int                               in_rx_seq_cnt      = 0;
  int                               checked_rx_seq_cnt = 0;
  local bit commit_exp_txn_at_txfifo_write = 0;
  local spi_mode_e                  prev_mode = Standard;
  int unsigned                      cur_trans_segments = 0;
  event event_sw_rst;

  // Callbacks
  spi_host_reg_cbs reg_cb;
  spi_host_mem_cbs mem_cb;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    plain_data_fifo  = new("plain_data_fifo", this);
    host_wr_segment = spi_segment_item::type_id::create("host_wr_segment");
    host_rd_segment = spi_segment_item::type_id::create("host_rd_segment");

    spi_ctrl_reg = '{default: '0};
    spi_ctrl_reg.rx_watermark = 8'h7f;
    foreach (initialise_configopts[i]) initialise_configopts[i] = 1'b1;

    // Instantiate and register callbacks
    reg_cb = new();
    reg_cb.sb = this;
    mem_cb = new();
    mem_cb.sb = this;

    uvm_reg_cb::add(ral.intr_state, reg_cb);
    uvm_reg_cb::add(ral.intr_enable, reg_cb);
    uvm_reg_cb::add(ral.intr_test, reg_cb);
    uvm_reg_cb::add(ral.control, reg_cb);
    uvm_reg_cb::add(ral.status, reg_cb);
    uvm_reg_cb::add(ral.configopts, reg_cb);
    uvm_reg_cb::add(ral.configopts_1, reg_cb);
    uvm_reg_cb::add(ral.csid, reg_cb);
    uvm_reg_cb::add(ral.command, reg_cb);
    uvm_reg_cb::add(ral.error_enable, reg_cb);
    uvm_reg_cb::add(ral.error_status, reg_cb);
    uvm_reg_cb::add(ral.event_enable, reg_cb);

    uvm_mem_cb::add(ral.txdata, mem_cb);
    uvm_mem_cb::add(ral.rxdata, mem_cb);
  endfunction

  virtual function bit is_sw_rst_active();
    return (spi_ctrl_reg.sw_rst !== 0) ||
           (cfg.force_spi_fsm_vif != null && cfg.force_spi_fsm_vif.fsm_sw_rst === 1'b1);
  endfunction

  virtual task wait_sw_rst_inactive();
    if (cfg.force_spi_fsm_vif != null) begin
      wait ((spi_ctrl_reg.sw_rst === 0) && (cfg.force_spi_fsm_vif.fsm_sw_rst !== 1'b1));
    end else begin
      wait (spi_ctrl_reg.sw_rst === 0);
    end
  endtask

  virtual task wait_no_reset();
    if (cfg.force_spi_fsm_vif != null) begin
      wait (cfg.clk_rst_vif.rst_n && (spi_ctrl_reg.sw_rst === 0) &&
            (cfg.force_spi_fsm_vif.fsm_sw_rst !== 1'b1));
    end else begin
      wait (cfg.clk_rst_vif.rst_n && (spi_ctrl_reg.sw_rst === 0));
    end
  endtask

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    wait (cfg.en_scb == 1);
    forever begin
      wait_no_reset();
      wait (cfg.spi_passthrough_vif.cio_csb_en_o === 1);
      `DV_SPINWAIT_EXIT(
        fork
          compare_tx_trans();
          compare_rx_trans();
          check_csn_lead();
          check_csn_idle();
        join,
        begin
          @(negedge cfg.clk_rst_vif.rst_n or event_sw_rst);
          if (!cfg.clk_rst_vif.rst_n) reset("HARD");
        end
      )
      `uvm_info(`gfn, "Restarting scoreboard checking due to reset event now.", UVM_LOW)
    end
  endtask : run_phase

  virtual function void apply_cs_agent_cfg(int cs_idx, spi_host_configopts_t cfg_opts);
    if (cs_idx >= 0 && cs_idx < SPI_HOST_NUM_CS) begin
      cfg.m_spi_agent_cfg.sck_polarity[cs_idx] = cfg_opts.cpol;
      cfg.m_spi_agent_cfg.sck_phase[cs_idx]    = cfg_opts.cpha;
      cfg.m_spi_agent_cfg.full_cyc[cs_idx]     = cfg_opts.fullcyc;
      cfg.m_spi_agent_cfg.csn_lead[cs_idx]     = cfg_opts.csnlead;
      cfg.m_spi_agent_cfg.csn_trail[cs_idx]    = cfg_opts.csntrail;
      cfg.m_spi_agent_cfg.csn_idle[cs_idx]     = cfg_opts.csnidle;
    end
  endfunction

  virtual task check_csn_idle_per_cs(int cs_idx);
    int unsigned num_quarter_cycles;
    int unsigned quarter_period;
    int unsigned half_period;
    spi_host_configopts_t cur_cfg;
    forever begin
      wait_sw_rst_inactive();
      @(posedge cfg.m_spi_agent_cfg.vif.csb[cs_idx]);
      if (!cfg.en_scb || (cfg.force_spi_fsm_vif != null && cfg.force_spi_fsm_vif.fast_mode == 1) ||
          is_sw_rst_active() || !cfg.clk_rst_vif.rst_n ||
          cfg.spi_passthrough_vif.cio_csb_en_o !== 1) begin
        continue;
      end
      cur_cfg = active_cs_configopts[cs_idx];
      half_period = (cur_cfg.clkdiv + 1) * cfg.clk_rst_vif.clk_period_ps;
      num_quarter_cycles = (cur_cfg.csnidle + 1) * 2;
      quarter_period = half_period / 2;
      for (int i = 0; i < num_quarter_cycles; i++) begin
        #(quarter_period * 1ps);
        if (!cfg.en_scb || is_sw_rst_active() || !cfg.clk_rst_vif.rst_n ||
            cfg.spi_passthrough_vif.cio_csb_en_o !== 1) begin
          break;
        end
        if (cfg.m_spi_agent_cfg.vif.csb[cs_idx] === 0) begin
          `uvm_error(`gfn, $sformatf("CS%0d (CONFIGOPTS.csnidle*2=%0d) > %0d 1/4 cycles since CSB=0x1.",
                                     cs_idx, num_quarter_cycles, i))
        end
      end
    end
  endtask

  virtual task check_csn_idle();
    for (int cs = 0; cs < SPI_HOST_NUM_CS; cs++) begin
      automatic int cs_idx = cs;
      fork
        check_csn_idle_per_cs(cs_idx);
      join_none
    end
    wait fork;
  endtask

  virtual task check_csn_lead_per_cs(int cs_idx);
    realtime start_time, end_time, last_sck_time, trail_end_time;
    longint unsigned meas_lead_ps, meas_trail_ps;
    longint unsigned exp_lead_ps, exp_trail_ps, half_period;
    spi_host_configopts_t cur_cfg;
    bit had_sck_edge;
    forever begin
      wait_sw_rst_inactive();
      @(negedge cfg.m_spi_agent_cfg.vif.csb[cs_idx]);
      start_time = $realtime();
      cur_cfg = active_cs_configopts[cs_idx];
      half_period = (cur_cfg.clkdiv + 1) * cfg.clk_rst_vif.clk_period_ps;
      exp_lead_ps = (cur_cfg.csnlead + 1) * half_period;
      had_sck_edge = 0;
      fork begin : wait_first_sck_or_csb
        fork
          begin
            @(cfg.m_spi_agent_cfg.vif.sck);
            had_sck_edge = 1;
          end
          begin
            @(posedge cfg.m_spi_agent_cfg.vif.csb[cs_idx]);
          end
        join_any
        disable fork;
      end join
      if (had_sck_edge) begin
        end_time = $realtime();
        last_sck_time = end_time;
        meas_lead_ps = longint'((end_time - start_time) / 1ps);
        if (cfg.en_scb && (cfg.force_spi_fsm_vif == null || cfg.force_spi_fsm_vif.fast_mode == 0) &&
            !is_sw_rst_active() && cfg.clk_rst_vif.rst_n === 1 &&
            cfg.spi_passthrough_vif.cio_csb_en_o === 1) begin
          if (meas_lead_ps < exp_lead_ps) begin
            `uvm_error(`gfn, $sformatf("Lead-time check failed (CS%0d): CSN asserted to SCK start %t < expected CSNLEAD %0d half sck cycles",
                       cs_idx, (end_time - start_time), cur_cfg.csnlead + 1))
          end
        end
        fork begin : wait_trail_csb
          fork
            forever begin
              @(cfg.m_spi_agent_cfg.vif.sck);
              if (cfg.m_spi_agent_cfg.vif.csb[cs_idx] === 1'b0) begin
                last_sck_time = $realtime();
              end
            end
            begin
              wait (cfg.m_spi_agent_cfg.vif.csb[cs_idx] === 1'b1);
            end
          join_any
          disable fork;
        end join
        trail_end_time = $realtime();
        meas_trail_ps = longint'((trail_end_time - last_sck_time) / 1ps);
        exp_trail_ps = (cur_cfg.csntrail + 1) * half_period;
        if (cfg.en_scb && (cfg.force_spi_fsm_vif == null || cfg.force_spi_fsm_vif.fast_mode == 0) &&
            !is_sw_rst_active() && cfg.clk_rst_vif.rst_n === 1 &&
            cfg.spi_passthrough_vif.cio_csb_en_o === 1) begin
          if (meas_trail_ps < exp_trail_ps) begin
            `uvm_error(`gfn, $sformatf("Trail-time check failed (CS%0d): last SCK edge to CSN deassert %t < expected CSNTRAIL %0d half sck cycles",
                       cs_idx, (trail_end_time - last_sck_time), cur_cfg.csntrail + 1))
          end
        end
      end
      fork
        begin
          automatic bit valid_xfer_done = had_sck_edge && !is_sw_rst_active() &&
                                          (cfg.clk_rst_vif.rst_n === 1'b1);
          #1ps;
          if (!is_sw_rst_active() && (cfg.clk_rst_vif.rst_n === 1'b1)) begin
            if (pending_lead_cfg_q[cs_idx].size() > 0) begin
              void'(pending_lead_cfg_q[cs_idx].pop_front());
            end else if (valid_xfer_done) begin
              early_csb_done_cnt[cs_idx]++;
            end
            if (pending_lead_cfg_q[cs_idx].size() > 0) begin
              active_cs_configopts[cs_idx] = pending_lead_cfg_q[cs_idx][0];
            end else begin
              active_cs_configopts[cs_idx] = spi_configopts_per_cs[cs_idx];
            end
            apply_cs_agent_cfg(cs_idx, active_cs_configopts[cs_idx]);
          end
        end
      join_none
    end
  endtask

  virtual task check_csn_lead();
    for (int cs = 0; cs < SPI_HOST_NUM_CS; cs++) begin
      automatic int cs_idx = cs;
      fork
        check_csn_lead_per_cs(cs_idx);
      join_none
    end
    wait fork;
  endtask

  task wait_start_sck_edge(int cs_idx = 0);
    int idx = (cs_idx >= 0 && cs_idx < SPI_HOST_NUM_CS) ? cs_idx : 0;
    if (active_cs_configopts[idx].cpol == active_cs_configopts[idx].cpha)
      @(negedge cfg.m_spi_agent_cfg.vif.sck);
    else
      @(posedge cfg.m_spi_agent_cfg.vif.sck);
  endtask

  virtual task get_next_plain_nibble(output logic [3:0] nibble);
    spi_item cur_item;
    forever begin
      if (plain_item == null) begin
        plain_data_fifo.get(plain_item);
      end
      cur_item = plain_item;
      wait (cur_item.plain_data_q.size() > 0 || cur_item.mon_item_complete);
      if (cur_item.plain_data_q.size() > 0) begin
        nibble = cur_item.plain_data_q.pop_front();
        return;
      end else begin
        plain_item = null;
      end
    end
  endtask : get_next_plain_nibble

  virtual task compare_rx_trans();
    spi_segment_item   tl_segment = spi_segment_item::type_id::create("tl_segment");
    string             txt = "";
    logic [7:0]        read_data;

    forever begin
      wait (read_segment_q.size() > 0);
      tl_segment = read_segment_q.pop_front();
      txt = "\n\t byte      SPI Bus     Bus Data";
      wait (rx_data_q.size() >= 4);
      if (rx_data_q.size == 0)
        `uvm_fatal(`gfn, "'rx_data_q.size' is empty - hence can't compare TXN")
      for (int i = 0; i < 4; i++) begin
        read_data = rx_data_q.pop_back();
        `uvm_info(`gfn, $sformatf("RX byte [%0d]: read_data=0x%02h, tl_data=0x%02h", i, read_data, tl_segment.spi_data[i]), UVM_DEBUG)
        if (read_data !== tl_segment.spi_data[i]) begin
          txt = {txt, $sformatf("\n \t [%d] \t\t\t      %0h  \t\t\t %0h", i, read_data, tl_segment.spi_data[i])};
          `uvm_error(`gfn, $sformatf("\n\t READ: actual data did not match exp data \n %s", txt))
        end else begin
          txt = {txt, $sformatf("\n \t [%d] \t\t\t %0h \t\t\t %0h", i, read_data, tl_segment.spi_data[i])};
        end
      end
      checked_rx_seq_cnt += 1;
      cfg.scb_checked_rx_seq_cnt = checked_rx_seq_cnt;
      `uvm_info(`gfn, $sformatf("\n successfully compared read transaction of %d ", tl_segment.command_reg.len+1), UVM_DEBUG)
    end
  endtask : compare_rx_trans

  virtual task extract_data_for_segment(spi_host_command_t command_info,
                                        output logic [7:0] host_data,
                                        output logic [7:0] device_data);
    logic [3:0] bus_cycle;
    int unsigned idx, loop_jump;
    host_data   = 8'h00;
    device_data = 8'h00;

    case (command_info.direction)
      None: begin
        get_next_plain_nibble(bus_cycle);
      end
      default: begin
        case (command_info.mode)
          Standard : loop_jump = 1;
          Dual     : loop_jump = 2;
          Quad     : loop_jump = 4;
          default  : `uvm_fatal(`gfn, $sformatf("Wrong command.speed: %s", command_info.mode.name()))
        endcase

        for (int i = 0; i < 8; i = i + loop_jump) begin
          bit bit_dir = (command_info.direction != RxOnly ?
                         cfg.m_spi_agent_cfg.host_bit_dir : cfg.m_spi_agent_cfg.device_bit_dir);
          idx = bit_dir ? i : (7 - i);

          get_next_plain_nibble(bus_cycle);
          case (command_info.mode)
            Standard: begin
              host_data[idx]   = bus_cycle[0];
              device_data[idx] = bus_cycle[1];
            end
            Dual: begin
              host_data[idx -: 2]   = bus_cycle[1:0];
              device_data[idx -: 2] = bus_cycle[1:0];
            end
            Quad: begin
              host_data[idx -: 4]   = bus_cycle[3:0];
              device_data[idx -: 4] = bus_cycle[3:0];
            end
            default: `uvm_fatal(`gfn, "Command.mode = Reserved")
          endcase
        end
        `uvm_info(`gfn, $sformatf("[%s] - Extracted byte-> host: 0x%0x | device: 0x%0x",
                                  command_info.mode.name, host_data, device_data), UVM_DEBUG)
      end
    endcase
  endtask : extract_data_for_segment

  virtual task compare_tx_trans();
    spi_segment_item exp_segment;
    string           txt = "";
    logic [7:0]      host_data;
    logic [7:0]      device_data;

    forever begin
      wait (write_segment_q.size > 0);
      exp_segment = write_segment_q.pop_front();
      in_tx_seg_cnt += 1;
      txt = "\n\t byte      actual     expected";
      for (int i = 0; i < exp_segment.command_reg.len + 1; i++) begin
        extract_data_for_segment(exp_segment.command_reg, host_data, device_data);

        if (exp_segment.command_reg.direction inside {TxOnly, Bidir}) begin
          bit [7:0] exp_byte;
          wait (tx_word_q.size() > 0);
          exp_byte = tx_word_q[0].bytes.pop_front();
          if (tx_word_q[0].bytes.size() == 0 || (i == exp_segment.command_reg.len)) begin
            void'(tx_word_q.pop_front());
          end
          if ($isunknown(host_data)) begin
            txt = {txt, $sformatf("\n \t [%d] \t\t\t      %b  \t\t\t %0h", i, host_data, exp_byte)};
            `uvm_error(`gfn, $sformatf("\n\t WRITE: floating/unknown value on active TX lane (mode=%s) - actual=%b exp=0x%02h \n len %d %s",
                                 exp_segment.command_reg.mode.name(), host_data, exp_byte,
                                 exp_segment.command_reg.len + 1, txt))
          end else if (host_data !== exp_byte) begin
            txt = {txt, $sformatf("\n \t [%d] \t\t\t      %0h  \t\t\t %0h", i, host_data, exp_byte)};
            `uvm_error(`gfn, $sformatf("\n\t WRITE: actual data did not match exp data \n len %d %s",
                                 exp_segment.command_reg.len + 1, txt))
          end else begin
            txt = {txt, $sformatf("\n \t [%d] \t\t\t %0h \t\t\t %0h", i, host_data, exp_byte)};
          end
        end

        if (exp_segment.command_reg.direction inside {RxOnly, Bidir}) begin
          rx_data_q.push_front(device_data);
        end
      end
      if ((exp_segment.command_reg.direction inside {RxOnly, Bidir}) &&
          ((exp_segment.command_reg.len + 1) % 4 != 0)) begin
        for (int n = 0; n < (4 - (exp_segment.command_reg.len + 1) % 4); n++) begin
          rx_data_q.push_front(8'h00);
        end
      end

      csaat = exp_segment.command_reg.csaat;

      if (cfg.en_cov) begin
        cov.config_opts_cg.sample(exp_segment.configopts);
        cov.different_ch_settings_cg.sample(exp_segment.csid, exp_segment.configopts);
      end

      if (cfg.force_spi_fsm_vif == null || cfg.force_spi_fsm_vif.fast_mode == 0) begin
        automatic bit seg_csaat = csaat;
        automatic bit [CSB_WIDTH-1:0] seg_csid = exp_segment.csid;
        automatic spi_host_configopts_t seg_cfg = exp_segment.configopts;
        automatic int seg_idx = checked_tx_seg_cnt + 1;
        fork
          begin
            check_csaat(.csaat(seg_csaat), .csid(seg_csid), .cfg_opts(seg_cfg), .seg_idx(seg_idx));
          end
        join_none
      end
      checked_tx_seg_cnt += 1;
      cfg.scb_checked_tx_seg_cnt = checked_tx_seg_cnt;
      `uvm_info(`gfn, $sformatf("\n successfully compared write transaction of %d ", exp_segment.command_reg.len + 1), UVM_HIGH)
    end
  endtask : compare_tx_trans

  virtual function bit is_core_stalled();
    uvm_hdl_data_t tx_st, rx_st;
    spi_host_status_t st;
    if (uvm_hdl_read("tb.dut.tx_stall", tx_st) && uvm_hdl_read("tb.dut.rx_stall", rx_st)) begin
      return (bit'(tx_st) || bit'(rx_st));
    end
    st = spi_host_status_t'(ral.status.get_mirrored_value());
    return (st.txstall || st.rxstall);
  endfunction

  virtual task check_csaat(bit csaat, bit [CSB_WIDTH-1:0] csid = 0,
                           spi_host_configopts_t cfg_opts = curr_spi_configopts,
                           int seg_idx = 0);
    if (!csaat) begin
      // CSAAT == 0: CSB[csid] must deassert to 1'b1 after WaitTrail ((csntrail + 2) half-SCK cycles),
      // and SCK must not keep ticking while CSB[csid] remains asserted low.
      int max_clks = ((cfg_opts.csntrail + 2) * (cfg_opts.clkdiv + 1)) + 50;
      bit saw_csb_deassert = (cfg.m_spi_agent_cfg.vif.csb[csid] === 1'b1);
      bit next_same_cs_queued = (write_segment_q.size() > 0 && write_segment_q[0].csid == csid) ||
                                (staged_cmd_q.size() > 0 && staged_cmd_q[0].csid == csid);

      if (saw_csb_deassert) return;

      fork begin : iso_fork_csaat0
        fork
          begin : csntrail_deassert_check
            for (int i = 0; i < max_clks; i++) begin
              if (!cfg.en_scb || !cfg.clk_rst_vif.rst_n || is_sw_rst_active() ||
                  cfg.spi_passthrough_vif.cio_csb_en_o !== 1) begin
                saw_csb_deassert = 1'b1;
                break;
              end
              if (cfg.m_spi_agent_cfg.vif.csb[csid] === 1'b1) begin
                saw_csb_deassert = 1'b1;
                break;
              end
              cfg.clk_rst_vif.wait_clks(1);
              if (cfg.m_spi_agent_cfg.vif.csb[csid] === 1'b1) begin
                saw_csb_deassert = 1'b1;
                break;
              end
              if (!spi_ctrl_reg.spien || (sw_error_bits != 6'b0) || is_core_stalled()) begin
                i--;
              end
            end

            if (!saw_csb_deassert && cfg.en_scb && cfg.clk_rst_vif.rst_n &&
                !is_sw_rst_active() && cfg.spi_passthrough_vif.cio_csb_en_o === 1) begin
              `uvm_error(`gfn, $sformatf("CSAAT=0 check failed (CS%0d): CSB still low %0d active clocks after last data sent",
                                         csid, max_clks))
            end
          end
          begin : extra_sck_check
            // At most 1 return-to-idle SCK edge can occur after the final SamplingEdge before CSB rises
            // (unless another same-CS segment was queued behind a sub-cycle clkdiv=0 pulse).
            int max_extra_sck_edges = next_same_cs_queued ? 50 : 3;
            repeat (max_extra_sck_edges) @(cfg.m_spi_agent_cfg.vif.sck);
            if (!saw_csb_deassert && cfg.m_spi_agent_cfg.vif.csb[csid] === 1'b0 &&
                !next_same_cs_queued && cfg.en_scb && cfg.clk_rst_vif.rst_n &&
                !is_sw_rst_active() && cfg.spi_passthrough_vif.cio_csb_en_o === 1) begin
              `uvm_error(`gfn, $sformatf("CSAAT=0 check failed (CS%0d): Clock kept ticking while CSB remained low",
                                         csid))
            end
          end
          begin : wait_csb_high
            wait (cfg.m_spi_agent_cfg.vif.csb[csid] === 1'b1);
            saw_csb_deassert = 1'b1;
          end
        join_any
        disable fork;
      end join
    end else begin
      // CSAAT == 1: CSB[csid] must remain asserted low (1'b0) across the post-segment trail window
      // unless a subsequent segment completes, a different-CSID command triggers a legal CS switch,
      // or reset/output-disable aborts it.
      int hold_clks = ((cfg_opts.csntrail + 1) * (cfg_opts.clkdiv + 1)) + 2;
      for (int k = 0; k < hold_clks; k++) begin
        bit cs_switch_pending;
        if (!cfg.en_scb || !cfg.clk_rst_vif.rst_n || is_sw_rst_active() ||
            !spi_ctrl_reg.output_en || cfg.spi_passthrough_vif.cio_csb_en_o !== 1) begin
          break;
        end
        if (seg_idx > 0 && checked_tx_seg_cnt > seg_idx) begin
          break;
        end
        cs_switch_pending = (spi_ctrl_reg.csid != csid) ||
                            (write_segment_q.size() > 0 && write_segment_q[0].csid != csid) ||
                            (staged_cmd_q.size() > 0 && staged_cmd_q[0].csid != csid);
        if (cs_switch_pending) begin
          break;
        end
        if (cfg.m_spi_agent_cfg.vif.csb[csid] !== 1'b0) begin
          `uvm_error(`gfn, $sformatf("CSAAT=1 check failed (CS%0d): CSB deasserted (0x%0b) prematurely %0d clocks after segment completion",
                                     csid, cfg.m_spi_agent_cfg.vif.csb[csid], k))
          break;
        end
        cfg.clk_rst_vif.wait_clks(1);
      end
    end
  endtask

  virtual task update_configopts(int cs_idx, spi_host_configopts_t next_spi_configopts);
    if (cs_idx >= 0 && cs_idx < SPI_HOST_NUM_CS) begin
      if (!initialise_configopts[cs_idx] && cfg.m_spi_agent_cfg.vif.csb[cs_idx] === 0) begin
        @(cfg.m_spi_agent_cfg.vif.csb[cs_idx]);
        cfg.clk_rst_vif.wait_clks(1);
      end
      initialise_configopts[cs_idx] = 1'b0;
      curr_spi_configopts = next_spi_configopts;
      spi_clk_half_period = (curr_spi_configopts.clkdiv + 1) * cfg.clk_rst_vif.clk_period_ps;
    end
  endtask

  // Promote commands queued in u_cmd_queue (staged_cmd_q) when u_spi_core is enabled (spien && !enb_error)
  virtual function void promote_staged_commands();
    if (!cfg.en_scb) begin
      staged_cmd_q.delete();
      return;
    end
    if (spi_ctrl_reg.sw_rst) begin
      staged_cmd_q.delete();
      return;
    end
    if (spi_ctrl_reg.spien && (sw_error_bits == 6'b0)) begin
      while (staged_cmd_q.size() > 0) begin
        spi_segment_item seg = staged_cmd_q.pop_front();
        if (spi_ctrl_reg.output_en) begin
          if (!prev_cmd_csaat || (seg.csid != prev_cmd_csid)) begin
            if (early_csb_done_cnt[seg.csid] > 0) begin
              early_csb_done_cnt[seg.csid]--;
              active_cs_configopts[seg.csid] = spi_configopts_per_cs[seg.csid];
              apply_cs_agent_cfg(seg.csid, active_cs_configopts[seg.csid]);
            end else begin
              pending_lead_cfg_q[seg.csid].push_back(seg.configopts);
              if (pending_lead_cfg_q[seg.csid].size() == 1) begin
                active_cs_configopts[seg.csid] = pending_lead_cfg_q[seg.csid][0];
                apply_cs_agent_cfg(seg.csid, active_cs_configopts[seg.csid]);
              end
            end
          end
          prev_cmd_csaat = seg.command_reg.csaat;
          prev_cmd_csid  = seg.csid;
          write_segment_q.push_back(seg);
          `uvm_info(`gfn, $sformatf("Promoted wr_segment (CS%0d):\n%s onto 'write_segment_q'",
                                    seg.csid, seg.convert2string()), UVM_DEBUG)
        end else begin
          // Core executes internally with external pads tri-stated (cio_csb_en_o == 0);
          // consume any TX FIFO bytes that u_spi_core drains internally.
          if (seg.command_reg.direction inside {TxOnly, Bidir}) begin
            for (int b = 0; b < seg.command_reg.len + 1; b++) begin
              if (tx_word_q.size() > 0) begin
                void'(tx_word_q[0].bytes.pop_front());
                if (tx_word_q[0].bytes.size() == 0 || (b == seg.command_reg.len)) begin
                  void'(tx_word_q.pop_front());
                end
              end
            end
          end
          prev_cmd_csaat = seg.command_reg.csaat;
          prev_cmd_csid  = seg.csid;
        end
      end
    end
  endfunction

  virtual function void reg_pre_write(string name, uvm_reg_data_t value);
    if (name == "control" || name == "sw_rst") begin
      if (cfg.force_spi_fsm_vif != null) begin
        was_active_at_pre_write = (cfg.force_spi_fsm_vif.fsm_state != 3'h0 &&
                                   cfg.force_spi_fsm_vif.fsm_state != 3'h7);
      end else begin
        uvm_hdl_data_t active_val;
        if (uvm_hdl_read("tb.dut.active", active_val)) begin
          was_active_at_pre_write = bit'(active_val);
        end else begin
          was_active_at_pre_write = bit'(get_field_val(ral.status.active, ral.status.get_mirrored_value()));
        end
      end
    end else if (name == "command") begin
      uvm_hdl_data_t busy_val;
      if (uvm_hdl_read("tb.dut.command_busy", busy_val)) begin
        was_cmd_busy_at_pre_write = bit'(busy_val);
      end else begin
        was_cmd_busy_at_pre_write = ((staged_cmd_q.size() + write_segment_q.size()) >= SPI_HOST_CMD_DEPTH);
      end
    end
  endfunction

  virtual function void mem_pre_write(string name);
    if (name == "txdata") begin
      uvm_hdl_data_t txready_val;
      if (uvm_hdl_read("tb.dut.tx_ready", txready_val)) begin
        was_txfull_at_pre_write = !bit'(txready_val);
      end else begin
        was_txfull_at_pre_write = (tx_word_q.size() >= (SPI_HOST_TX_DEPTH + 1));
      end
    end
  endfunction

  virtual function void mem_pre_read(string name);
    if (name == "rxdata") begin
      uvm_hdl_data_t rxvalid_val;
      if (uvm_hdl_read("tb.dut.rx_valid", rxvalid_val)) begin
        was_rxempty_at_pre_read = !bit'(rxvalid_val);
      end else begin
        was_rxempty_at_pre_read = (rx_data_q.size() == 0 && write_segment_q.size() == 0 &&
                                   staged_cmd_q.size() == 0 && in_tx_seg_cnt == checked_tx_seg_cnt);
      end
    end
  endfunction

  // Callback methods implementation: Register Write
  virtual function void reg_write(string name, uvm_reg_data_t value);
    `uvm_info(`gfn, $sformatf("Reg Write callback: %s = 0x%0h", name, value), UVM_HIGH)
    case (name)
      "control", "sw_rst": begin
        if (name == "sw_rst") begin
          spi_ctrl_reg.sw_rst = bit'(value);
        end else begin
          spi_ctrl_reg.rx_watermark = get_field_val(ral.control.rx_watermark, value);
          spi_ctrl_reg.tx_watermark = get_field_val(ral.control.tx_watermark, value);
          spi_ctrl_reg.output_en    = get_field_val(ral.control.output_en, value);
          spi_ctrl_reg.spien        = get_field_val(ral.control.spien, value);
          spi_ctrl_reg.sw_rst       = get_field_val(ral.control.sw_rst, value);
          void'(ral.control.predict(.value(value), .kind(UVM_PREDICT_WRITE)));
        end

        if (cfg.en_cov) begin
          uvm_hdl_data_t active_val;
          bit active;
          if (spi_ctrl_reg.sw_rst) begin
            active = was_active_at_pre_write;
          end else if (cfg.force_spi_fsm_vif != null) begin
            active = (cfg.force_spi_fsm_vif.fsm_state != 3'h0 &&
                      cfg.force_spi_fsm_vif.fsm_state != 3'h7);
          end else if (uvm_hdl_read("tb.dut.active", active_val)) begin
            active = bit'(active_val);
          end else begin
            active = bit'(get_field_val(ral.status.active, ral.status.get_mirrored_value()));
          end
          cov.control_cg.sample(spi_ctrl_reg, active);
        end

        if (spi_ctrl_reg.sw_rst) begin
          `uvm_info(`gfn, "SW reset detected", UVM_LOW)
          ->event_sw_rst;
          reset("SOFT");
        end else begin
          promote_staged_commands();
        end
      end
      "configopts", "configopts_1": begin
        int cs_idx = (name == "configopts_1") ? 1 : 0;
        uvm_reg cfg_reg = (name == "configopts_1") ? uvm_reg'(ral.configopts_1) : uvm_reg'(ral.configopts);
        spi_configopts.cpol     = value[31];
        spi_configopts.cpha     = value[30];
        spi_configopts.fullcyc  = value[29];
        spi_configopts.csnlead  = value[27:24];
        spi_configopts.csntrail = value[23:20];
        spi_configopts.csnidle  = value[19:16];
        spi_configopts.clkdiv   = value[15:0];
        if (cs_idx < SPI_HOST_NUM_CS) begin
          automatic int target_cs = cs_idx;
          automatic spi_host_configopts_t next_opts = spi_configopts;
          spi_configopts_per_cs[cs_idx] = spi_configopts;
          if (pending_lead_cfg_q[cs_idx].size() == 0) begin
            active_cs_configopts[cs_idx] = spi_configopts;
            apply_cs_agent_cfg(cs_idx, spi_configopts);
          end
          fork
            begin
              update_configopts(target_cs, next_opts);
            end
          join_none
        end
        void'(cfg_reg.predict(.value(value), .kind(UVM_PREDICT_WRITE)));
      end
      "command": begin
        bit csid_inval;
        bit cmd_inval;
        bit cmd_busy;
        int unsigned cmd_csid = (spi_ctrl_reg.csid < SPI_HOST_NUM_CS) ? spi_ctrl_reg.csid : 0;
        spi_cmd_reg.direction = spi_dir_e'(get_field_val(ral.command.direction, value));
        spi_cmd_reg.mode      = spi_mode_e'(get_field_val(ral.command.speed, value));
        spi_cmd_reg.csaat     = get_field_val(ral.command.csaat, value);
        spi_cmd_reg.len       = get_field_val(ral.command.len, value);

        host_wr_segment.command_reg.len       = spi_cmd_reg.len;
        host_wr_segment.command_reg.direction = spi_cmd_reg.direction;
        host_wr_segment.command_reg.mode      = spi_cmd_reg.mode;
        host_wr_segment.command_reg.csaat     = spi_cmd_reg.csaat;
        host_wr_segment.csid                  = cmd_csid[CSB_WIDTH-1:0];
        host_wr_segment.configopts            = spi_configopts_per_cs[cmd_csid];

        cmd_busy   = was_cmd_busy_at_pre_write;
        csid_inval = !cmd_busy && (spi_ctrl_reg.csid >= SPI_HOST_NUM_CS);
        cmd_inval  = !cmd_busy && (!(spi_cmd_reg.mode inside {Standard, Dual, Quad}) ||
                                   (spi_cmd_reg.mode != Standard && spi_cmd_reg.direction == Bidir));

        if (cmd_busy)   sw_error_bits[0] = 1'b1;
        if (cmd_inval)  sw_error_bits[3] = 1'b1;
        if (csid_inval) sw_error_bits[4] = 1'b1;

        // Per RTL spi_host.sv:189-263, commands written while !command_busy enter u_cmd_queue
        // regardless of CONTROL.OUTPUT_EN; invalid CSID clamps csid to 0 while setting enb_error.
        if (cfg.en_scb && !cmd_busy && !cmd_inval) begin
          spi_segment_item wr_segment;
          `downcast(wr_segment, host_wr_segment.clone());
          staged_cmd_q.push_back(wr_segment);
          host_wr_segment = spi_segment_item::type_id::create("host_wr_segment");
          promote_staged_commands();
        end
        if (cfg.en_cov) begin
          uvm_hdl_data_t tx_qd_val;
          bit extra_data;
          void'(uvm_hdl_read("tb.dut.tx_qd", tx_qd_val));
          extra_data = (cur_tx_fifo_bytes > (spi_cmd_reg.len + 1)) ||
                       (tx_qd_val * 4 > (spi_cmd_reg.len + 1)) || (tx_qd_val > 1);
          if (!cmd_busy && !cmd_inval && !csid_inval &&
              (spi_cmd_reg.direction inside {TxOnly, Bidir})) begin
            int bytes_sent = spi_cmd_reg.len + 1;
            cur_tx_fifo_bytes = (cur_tx_fifo_bytes > bytes_sent) ? (cur_tx_fifo_bytes - bytes_sent) : 0;
          end
          cur_trans_segments++;
          cov.duplex_cg.sample(spi_cmd_reg.direction);
          cov.command_cg.sample(spi_cmd_reg);
          cov.command_segment_cg.sample(spi_cmd_reg);
          cov.segment_speed_cg.sample(prev_mode, spi_cmd_reg.mode);
          cov.num_segment_cg.sample(cur_trans_segments, spi_cmd_reg.len, extra_data);
          prev_mode = spi_cmd_reg.mode;
          if (!spi_cmd_reg.csaat) cur_trans_segments = 0;
        end
      end
      "intr_enable": begin
        spi_intr_enable_reg.spi_event  = bit'(get_field_val(ral.intr_enable.spi_event, value));
        spi_intr_enable_reg.error      = bit'(get_field_val(ral.intr_enable.error, value));
        void'(ral.intr_enable.predict(.value(value), .kind(UVM_PREDICT_DIRECT)));
      end
      "intr_state": begin
        bit [NumSpiHostIntr-1:0] cur_state = `gmv(ral.intr_state);
        bit [NumSpiHostIntr-1:0] new_state = cur_state & ~value[NumSpiHostIntr-1:0];
        void'(ral.intr_state.predict(.value(new_state), .kind(UVM_PREDICT_DIRECT)));
      end
      "intr_test": begin
        spi_intr_test_reg.spi_event  = bit'(get_field_val(ral.intr_test.spi_event, value));
        spi_intr_test_reg.error      = bit'(get_field_val(ral.intr_test.error, value));
        if (cfg.en_cov) begin
          bit [31:0] intr_en = `gmv(ral.intr_enable);
          bit [NumSpiHostIntr-1:0] intr_exp = value | `gmv(ral.intr_state);
          void'(ral.intr_state.predict(.value(intr_exp), .kind(UVM_PREDICT_DIRECT)));
          foreach (intr_exp[i]) begin
            cov.intr_test_cg.sample(i, value[i], intr_en[i], intr_exp[i]);
          end
        end
      end
      "csid": begin
        spi_ctrl_reg.csid = value;
        void'(ral.csid.predict(.value(value), .kind(UVM_PREDICT_WRITE)));
        if (cfg.en_cov) cov.csid_cg.sample(spi_ctrl_reg);
      end
      "error_enable": begin
        spi_error_enable_reg.csidinval = bit'(get_field_val(ral.error_enable.csidinval, value));
        spi_error_enable_reg.cmdinval  = bit'(get_field_val(ral.error_enable.cmdinval, value));
        spi_error_enable_reg.underflow = bit'(get_field_val(ral.error_enable.underflow, value));
        spi_error_enable_reg.overflow  = bit'(get_field_val(ral.error_enable.overflow, value));
        spi_error_enable_reg.cmdbusy   = bit'(get_field_val(ral.error_enable.cmdbusy, value));
        void'(ral.error_enable.predict(.value(value), .kind(UVM_PREDICT_WRITE)));
        if (cfg.en_cov) cov.error_en_cg.sample(spi_error_enable_reg);
      end
      "error_status": begin
        sw_error_bits &= ~value[5:0];
        void'(ral.error_status.predict(.value(value), .kind(UVM_PREDICT_WRITE)));
        promote_staged_commands();
      end
      "event_enable": begin
        spi_event_enable_reg.idle      = bit'(get_field_val(ral.event_enable.idle, value));
        spi_event_enable_reg.ready     = bit'(get_field_val(ral.event_enable.ready, value));
        spi_event_enable_reg.txwm      = bit'(get_field_val(ral.event_enable.txwm, value));
        spi_event_enable_reg.rxwm      = bit'(get_field_val(ral.event_enable.rxwm, value));
        spi_event_enable_reg.txempty   = bit'(get_field_val(ral.event_enable.txempty, value));
        spi_event_enable_reg.rxfull    = bit'(get_field_val(ral.event_enable.rxfull, value));
        void'(ral.event_enable.predict(.value(value), .kind(UVM_PREDICT_WRITE)));
        if (cfg.en_cov) cov.event_en_cg.sample(spi_event_enable_reg);
      end
    endcase
  endfunction

  // Callback methods implementation: Register Read
  virtual function void reg_read(string name, uvm_reg_data_t value);
    `uvm_info(`gfn, $sformatf("Reg Read callback: %s = 0x%0h", name, value), UVM_HIGH)
    case (name)
      "intr_state": begin
         spi_intr_state_reg.spi_event  = bit'(get_field_val(ral.intr_state.spi_event, value));
         spi_intr_state_reg.error      = bit'(get_field_val(ral.intr_state.error, value));
         void'(ral.intr_state.predict(.value(value), .kind(UVM_PREDICT_READ)));
         if (cfg.en_cov) begin
           bit [31:0]               intr_en  = `gmv(ral.intr_enable);
           bit [NumSpiHostIntr-1:0] intr_exp = `gmv(ral.intr_state);
           foreach (intr_exp[i]) begin
             cov.intr_cg.sample(i, intr_en[i], value[i]);
             cov.intr_pins_cg.sample(i, cfg.intr_vif.pins[i]);
           end
         end
       end
      "error_status": begin
        sw_error_bits = value[5:0];
        spi_error_status_reg.accessinval = bit'(get_field_val(ral.error_status.accessinval, value));
        spi_error_status_reg.csidinval   = bit'(get_field_val(ral.error_status.csidinval, value));
        spi_error_status_reg.cmdinval    = bit'(get_field_val(ral.error_status.cmdinval, value));
        spi_error_status_reg.underflow   = bit'(get_field_val(ral.error_status.underflow, value));
        spi_error_status_reg.overflow    = bit'(get_field_val(ral.error_status.overflow, value));
        spi_error_status_reg.cmdbusy     = bit'(get_field_val(ral.error_status.cmdbusy, value));
        void'(ral.error_status.predict(.value(value), .kind(UVM_PREDICT_READ)));
        if (|(value & (ral.error_enable.get_mirrored_value() | 32'h20))) begin
          void'(ral.intr_state.error.predict(.value(1'b1), .kind(UVM_PREDICT_DIRECT)));
        end
        if (cfg.en_cov) cov.error_status_cg.sample(spi_error_status_reg, spi_error_enable_reg);
      end
      "status": begin
        spi_status_reg.ready       = get_field_val(ral.status.ready, value);
        spi_status_reg.active      = get_field_val(ral.status.active, value);
        spi_status_reg.txfull      = get_field_val(ral.status.txfull, value);
        spi_status_reg.txempty     = get_field_val(ral.status.txempty, value);
        spi_status_reg.txstall     = get_field_val(ral.status.txstall, value);
        spi_status_reg.tx_wm       = get_field_val(ral.status.txwm, value);
        spi_status_reg.rxfull      = get_field_val(ral.status.rxfull, value);
        spi_status_reg.rxempty     = get_field_val(ral.status.rxempty, value);
        spi_status_reg.rxstall     = get_field_val(ral.status.rxstall, value);
        spi_status_reg.byteorder   = get_field_val(ral.status.byteorder, value);
        spi_status_reg.rx_wm       = get_field_val(ral.status.rxwm, value);
        spi_status_reg.cmd_qd      = get_field_val(ral.status.cmdqd, value);
        spi_status_reg.rx_qd       = get_field_val(ral.status.rxqd, value);
        spi_status_reg.tx_qd       = get_field_val(ral.status.txqd, value);
        void'(ral.status.predict(.value(value), .kind(UVM_PREDICT_READ)));
        if (cfg.en_cov) cov.status_cg.sample(spi_status_reg);
      end
    endcase
  endfunction

  function bit is_valid_tx_mask(bit [3:0] mask);
    return spi_host_env_pkg::is_valid_mask(mask, 1'b1);
  endfunction

  // Callback methods implementation: Memory Write
  virtual function void mem_write(string name, uvm_reg_addr_t offset, uvm_reg_data_t value, uvm_reg_byte_en_t byte_en);
    `uvm_info(`gfn, $sformatf("Mem Write callback: %s [offset 0x%0h] = 0x%0h (be: 0x%0h)", name, offset, value, byte_en), UVM_HIGH)
    if (name == "txdata") begin
      bit [7:0] bytes[4] = {<< 8{value}};
      bit mask_ok = is_valid_tx_mask(byte_en[3:0]);

      if (cfg.en_cov) begin
        spi_host_status_t status;
        uvm_hdl_data_t txfull_val;
        if (was_txfull_at_pre_write) begin
          status.txfull = 1'b1;
        end else if (uvm_hdl_read("tb.dut.tx_full", txfull_val)) begin
          status.txfull = bit'(txfull_val);
        end else begin
          status = spi_host_status_t'(ral.status.get_mirrored_value());
        end
        cov.tx_fifo_overflow_cg.sample(status);
        cov.unaligned_data_cg.sample(byte_en[3:0]);
      end

      if (!mask_ok) begin
        sw_error_bits[5] = 1'b1;
      end
      if (was_txfull_at_pre_write) begin
        sw_error_bits[1] = 1'b1;
      end

      if (mask_ok && !was_txfull_at_pre_write && (tx_word_q.size() < SPI_HOST_TX_DEPTH + 1)) begin
        tx_word_t w;
        foreach (bytes[i]) begin
          if (byte_en[i]) begin
            w.bytes.push_back(bytes[i]);
            cur_tx_fifo_bytes++;
            `uvm_info(`gfn, $sformatf("Write to TXFIFO: 0x%0x", bytes[i]), UVM_DEBUG)
          end
        end
        tx_word_q.push_back(w);
      end
    end
  endfunction

  // Callback methods implementation: Memory Read
  virtual function void mem_read(string name, uvm_reg_addr_t offset, uvm_reg_data_t value);
    `uvm_info(`gfn, $sformatf("Mem Read callback: %s [offset 0x%0h] = 0x%0h", name, offset, value), UVM_HIGH)
    if (name == "rxdata") begin
      bit [7:0] bytes[4] = {<< 8{value}};

      if (cfg.en_cov) begin
        spi_host_status_t status;
        uvm_hdl_data_t rxempty_val;
        if (was_rxempty_at_pre_read) begin
          status.rxempty = 1'b1;
        end else if (uvm_hdl_read("tb.dut.rx_empty", rxempty_val)) begin
          status.rxempty = bit'(rxempty_val);
        end else begin
          status = spi_host_status_t'(ral.status.get_mirrored_value());
        end
        cov.rx_fifo_underflow_cg.sample(status);
      end

      if (was_rxempty_at_pre_read) begin
        sw_error_bits[2] = 1'b1;
      end else if (cfg.en_scb && (rx_data_q.size() > 0 || write_segment_q.size() > 0 ||
                                  staged_cmd_q.size() > 0 || in_tx_seg_cnt > checked_tx_seg_cnt)) begin
        spi_segment_item rd_segment;
        host_rd_segment.spi_data.delete();
        foreach (bytes[i]) begin
          host_rd_segment.spi_data.push_back(bytes[i]);
          `uvm_info(`gfn, $sformatf("Read from RXFIFO: 0x%0x", bytes[i]), UVM_DEBUG)
        end
        `downcast(rd_segment, host_rd_segment.clone());
        read_segment_q.push_back(rd_segment);
        in_rx_seq_cnt += 1;
      end
    end
  endfunction

  virtual function void reset(string kind = "HARD");
    for (int i = 0; i < SPI_HOST_NUM_CS; i++) begin
      pending_lead_cfg_q[i].delete();
      early_csb_done_cnt[i]    = 0;
      initialise_configopts[i] = 1'b1;
    end
    prev_cmd_csaat = 0;
    prev_cmd_csid  = 0;
    if (kind == "HARD") begin
      super.reset(kind);
      void'(ral.intr_state.predict(.value(2'b00), .kind(UVM_PREDICT_DIRECT)));
      spi_ctrl_reg = '{default: '0};
      spi_ctrl_reg.rx_watermark = 8'h7f;
      sw_error_bits = 6'b0;
      spi_configopts = '{default: '0};
      for (int i = 0; i < SPI_HOST_NUM_CS; i++) begin
        spi_configopts_per_cs[i] = '{default: '0};
        active_cs_configopts[i]  = '{default: '0};
        apply_cs_agent_cfg(i, active_cs_configopts[i]);
      end
    end else begin
      for (int i = 0; i < SPI_HOST_NUM_CS; i++) begin
        active_cs_configopts[i] = spi_configopts_per_cs[i];
        apply_cs_agent_cfg(i, active_cs_configopts[i]);
      end
    end
    plain_data_fifo.flush();
    staged_cmd_q.delete();
    write_segment_q.delete();
    read_segment_q.delete();
    tx_word_q.delete();
    rx_data_q.delete();
    host_wr_segment = spi_segment_item::type_id::create("host_wr_segment");
    host_rd_segment = spi_segment_item::type_id::create("host_rd_segment");
    plain_item = null;
    in_tx_seg_cnt = checked_tx_seg_cnt;
    in_rx_seq_cnt = checked_rx_seq_cnt;
    cur_trans_segments = 0;
    cur_tx_fifo_bytes = 0;
  endfunction : reset

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    if (cfg.en_scb) begin
      if (in_tx_seg_cnt != checked_tx_seg_cnt)
        `uvm_error(`gfn, $sformatf("Didn't check all segments - expected %0d actual %0d", in_tx_seg_cnt, checked_tx_seg_cnt))
      if (in_rx_seq_cnt != checked_rx_seq_cnt)
        `uvm_error(`gfn, $sformatf("Didn't check all RX reads - expected %0d actual %0d", in_rx_seq_cnt, checked_rx_seq_cnt))

      `DV_EOT_PRINT_Q_CONTENTS(spi_segment_item, staged_cmd_q)
      `DV_EOT_PRINT_Q_CONTENTS(spi_segment_item, write_segment_q)
      `DV_EOT_PRINT_Q_CONTENTS(spi_segment_item, read_segment_q)
      `DV_EOT_PRINT_TLM_FIFO_CONTENTS(spi_item, plain_data_fifo)
      if ((rx_data_q.size() != 0))
        `uvm_fatal(`gfn, $sformatf("ERROR - RX FIFO in DUT still has data to be read! (rx_data_q = %0d)", rx_data_q.size()))
    end
  endfunction : check_phase

endclass : spi_host_scoreboard
