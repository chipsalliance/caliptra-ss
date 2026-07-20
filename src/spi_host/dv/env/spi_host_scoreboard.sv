// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Forward declaration of scoreboard
typedef class spi_host_scoreboard;

class spi_host_reg_cbs extends uvm_reg_cbs;
  spi_host_scoreboard sb;
  
  virtual task post_write(uvm_reg_item rw);
    sb.reg_write(rw.element.get_name(), rw.value[0]);
  endtask

  virtual task post_read(uvm_reg_item rw);
    sb.reg_read(rw.element.get_name(), rw.value[0]);
  endtask
endclass

class spi_host_mem_cbs extends uvm_reg_cbs;
  spi_host_scoreboard sb;

  virtual task post_write(uvm_reg_item rw);
    // TODO (Caliptra port): uvm_reg_item in standard UVM 1.2 does not contain byte_en.
    // For now we pass 4'hf (all bytes enabled) to compile. Scoreboard verification for
    // partial writes via callbacks will need alternative tracking (e.g. AXI agent monitoring
    // or custom extension).
    sb.mem_write(rw.element.get_name(), rw.offset, rw.value[0], 4'hf);
  endtask

  virtual task post_read(uvm_reg_item rw);
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
  local spi_segment_item            write_segment_q[$];
  local spi_segment_item            read_segment_q[$];
  local bit [7:0]                   rx_data_q[$];
  local bit                         csaat = 0;
  local int                         spi_clk_half_period;

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
  spi_host_configopts_t             curr_spi_configopts;
  bit                               initialise_configopts = 1;

  // Tally-Counters
  int                               in_tx_seg_cnt      = 0;
  int                               checked_tx_seg_cnt = 0;
  int                               in_rx_seq_cnt      = 0;
  int                               checked_rx_seq_cnt = 0;
  local bit commit_exp_txn_at_txfifo_write = 0;
  event event_sw_rst;

  // Callbacks
  spi_host_reg_cbs reg_cb;
  spi_host_mem_cbs mem_cb;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    plain_data_fifo  = new("plain_data_fifo", this);
    host_wr_segment = spi_segment_item::type_id::create("host_wr_segment");
    host_rd_segment = spi_segment_item::type_id::create("host_rd_segment");

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
    uvm_reg_cb::add(ral.csid, reg_cb);
    uvm_reg_cb::add(ral.command, reg_cb);
    uvm_reg_cb::add(ral.error_enable, reg_cb);
    uvm_reg_cb::add(ral.error_status, reg_cb);
    uvm_reg_cb::add(ral.event_enable, reg_cb);

    uvm_mem_cb::add(ral.txdata, mem_cb);
    uvm_mem_cb::add(ral.rxdata, mem_cb);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    wait (cfg.en_scb == 1);
    forever begin
      wait(cfg.clk_rst_vif.rst_n && !spi_ctrl_reg.sw_rst);
      wait (cfg.spi_passthrough_vif.cio_csb_en_o === 1);
      `DV_SPINWAIT_EXIT(
        fork
          compare_tx_trans();
          compare_rx_trans();
          get_plain_txn();
          check_csn_lead();
          check_csn_idle();
        join,
        @(negedge cfg.clk_rst_vif.rst_n or event_sw_rst)
      )
      `uvm_info(`gfn, "Restarting scoreboard checking due to reset event now.", UVM_LOW)
    end
  endtask : run_phase

  virtual task check_csn_idle();
    int unsigned num_quarter_cycles;
    int unsigned quarter_period;
    forever begin
      wait (spi_ctrl_reg.sw_rst === 0);
      @(posedge cfg.m_spi_agent_cfg.vif.csb[0]);
      if (cfg.force_spi_fsm_vif.fast_mode == 1) continue;
      num_quarter_cycles = (curr_spi_configopts.csnidle + 1) * 2;
      quarter_period = spi_clk_half_period / 2;
      for(int i = 0; i < num_quarter_cycles; i++) begin
        #(quarter_period * 1ps);
        if (cfg.m_spi_agent_cfg.vif.csb[0] === 0) begin
          `uvm_error(`gfn, $sformatf("(CONFIGOPTS.csnidle*2=%0d) > %0d 1/4 cycles since CSB=0x1.", num_quarter_cycles, i))
        end
      end
    end
  endtask

  virtual task check_csn_lead();
    time start_time, end_time;
    int unsigned quarter_period;
    forever begin
      wait (spi_ctrl_reg.sw_rst === 0);
      @(negedge cfg.m_spi_agent_cfg.vif.csb[0]);
      start_time = $realtime();
      @(posedge cfg.m_spi_agent_cfg.vif.sck);
      end_time = $realtime();
      if (cfg.force_spi_fsm_vif.fast_mode == 1) continue;
      quarter_period = spi_clk_half_period / 2;
      if ((end_time - start_time) < (curr_spi_configopts.csnlead + 1) * spi_clk_half_period * 1ps) begin
        `uvm_error(`gfn, $sformatf("Lead-time check failed: CSN asserted to SCK start %t < expected CSNLEAD %d half sck cycles", 
                   (end_time - start_time), curr_spi_configopts.csnlead + 1))
      end
    end
  endtask

  task wait_start_sck_edge();
    if (spi_configopts.cpol == spi_configopts.cpha)
      @(negedge cfg.m_spi_agent_cfg.vif.sck);
    else
      @(posedge cfg.m_spi_agent_cfg.vif.sck);
  endtask

  virtual task get_plain_txn();
    forever begin
      plain_data_fifo.get(plain_item);
      `uvm_info(`gfn, $sformatf("Received: plain_item=\n%s", plain_item.sprint), UVM_DEBUG)
    end
  endtask : get_plain_txn

  virtual task compare_rx_trans();
    spi_segment_item   tl_segment = spi_segment_item::type_id::create("tl_segment");
    string             txt = "";
    bit [7:0]          read_data;

    forever begin
      wait (read_segment_q.size() > 0);
      tl_segment = read_segment_q.pop_front();
      txt = "\n\t byte      SPI Bus     Bus Data";
      if (rx_data_q.size == 0)
        `uvm_fatal(`gfn, "'rx_data_q.size' is empty - hence can't compare TXN")
      for ( int i = 0; i < 4; i++) begin
        read_data = rx_data_q.pop_back();
        if (read_data != tl_segment.spi_data[i]) begin
          txt = {txt, $sformatf("\n \t [%0d] \t %2h \t %2h", i, read_data, tl_segment.spi_data[i])};
          `uvm_fatal(`gfn, $sformatf("\n\tREAD:  SPI bus data %0h did not match bus data %0h \n len %d %s",
                               read_data, tl_segment.spi_data[i], tl_segment.command_reg.len+1, txt))
        end else begin
          txt = {txt, $sformatf("\n \t [%0d] \t %2h \t %2h", i, read_data, tl_segment.spi_data[i])};
        end
      end
      `uvm_info(`gfn, $sformatf("\n successfully compared read transaction of %d ", tl_segment.command_reg.len+1), UVM_DEBUG)
    end
  endtask : compare_rx_trans

  virtual task  extract_data_for_segment(spi_host_command_t  command_info,
                                         output bit[7:0] host_data, output bit [7:0] device_data);
    bit [3:0] bus_cycle;
    int unsigned idx, loop_jump;

    if (plain_item == null) `uvm_fatal(`gfn, "Something's wrong: 'plain_item =  null'")

    case (command_info.direction)
      None: begin
        wait(plain_item.plain_data_q.size >= 1);
        void'(plain_item.plain_data_q.pop_front());
      end
      default: begin
        case (command_info.mode)
          Standard : loop_jump = 1;
          Dual     : loop_jump = 2;
          Quad     : loop_jump = 4;
          default  : `uvm_fatal(`gfn, $sformatf("Wrong command.speed: %s",command_info.mode.name()))
        endcase
        wait(plain_item.plain_data_q.size >= (8 / loop_jump) );

        for (int i = 0; i < 8; i = i + loop_jump) begin
          bit bit_dir = (command_info.direction != RxOnly ?
                         cfg.m_spi_agent_cfg.host_bit_dir : cfg.m_spi_agent_cfg.device_bit_dir);
          idx = bit_dir ? i : (7 - i);

          bus_cycle = plain_item.plain_data_q.pop_front();
          case (command_info.mode)
            Standard: begin
              host_data[idx]   = bus_cycle[0];
              device_data[idx] = bus_cycle[1];
            end
            Dual: begin
              host_data[idx -: 2] = bus_cycle[1:0];
              device_data[idx -: 2] = bus_cycle[1:0];
            end
            Quad: begin
              host_data[idx -: 4] = bus_cycle[3:0];
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
    string             txt = "";
    bit [7:0]          host_data;
    bit [7:0]          device_data;

    forever begin
      wait (write_segment_q.size > 0);
      exp_segment = write_segment_q.pop_front();
      in_tx_seg_cnt += 1;
      txt = "\n\t byte      actual     expected";
      for (int i=0; i < exp_segment.command_reg.len+1; i++) begin
        wait(&cfg.m_spi_agent_cfg.vif.csb == 0);
        cfg.m_spi_agent_cfg.wait_sck_edge(SamplingEdge, cfg.m_spi_agent_cfg.vif.get_active_csb());
        extract_data_for_segment(exp_segment.command_reg, host_data, device_data);

        if (exp_segment.command_reg.direction inside {TxOnly, Bidir}) begin
          if (host_data != exp_segment.spi_data[i]) begin
            txt = {txt, $sformatf("\n \t [%d] \t\t\t      %0h  \t\t\t %0h", i, host_data, exp_segment.spi_data[i])};
            `uvm_fatal(`gfn, $sformatf("\n\t WRITE: actual data did not match exp data \n len %d %s",
                                 exp_segment.command_reg.len+1, txt))
          end else begin
            txt = {txt, $sformatf("\n \t [%d] \t\t\t %0h \t\t\t %0h", i, host_data, exp_segment.spi_data[i])};
          end
        end

        if (exp_segment.command_reg.direction inside {RxOnly, Bidir}) begin
          rx_data_q.push_front(device_data);
        end
      end
      if ((exp_segment.command_reg.direction inside {RxOnly, Bidir})
          && ((exp_segment.command_reg.len+1)%4 != 0)) begin
        for (int n=0; n<(4-(exp_segment.command_reg.len+1)%4); n++) begin
          rx_data_q.push_front(8'h00);
        end
      end

      csaat = exp_segment.command_reg.csaat;

      if (cfg.force_spi_fsm_vif.fast_mode == 0) begin
        fork
          begin
            check_csaat(.csaat(csaat));
          end
        join_none
      end
      checked_tx_seg_cnt += 1;
      `uvm_info(`gfn, $sformatf("\n successfully compared write transaction of %d ", exp_segment.command_reg.len+1), UVM_HIGH)
    end
  endtask : compare_tx_trans

  virtual task check_csaat(bit csaat);
    int num_times = ((curr_spi_configopts.csntrail + 1 + 1) * (curr_spi_configopts.clkdiv + 1)) + 1;
    spi_host_status_t status;

    fork begin : iso_fork
      fork
        begin : csntrail_check
          bit stall_flag;
          for (int i=0; i < num_times; i++) begin
            status = spi_host_status_t'(ral.status.get_mirrored_value());

            if (spi_ctrl_reg.spien==0) begin
              wait (spi_ctrl_reg.spien === 1);
              if (i > 0) stall_flag = 1;
            end
            else if (status.txstall || status.rxstall) begin
              stall_flag = 1;
            end

            if (cfg.m_spi_agent_cfg.vif.csb[0] !== csaat) break;
            cfg.clk_rst_vif.wait_clks(1);
            if (stall_flag) i--;
          end

          status = spi_host_status_t'(ral.status.get_mirrored_value());
          if (spi_ctrl_reg.spien === 0) begin
            wait (spi_ctrl_reg.spien === 1);
            #(spi_clk_half_period/2 * 1ps);
          end
          #(spi_clk_half_period/2 * 1ps);

          if (cfg.m_spi_agent_cfg.vif.csb[0] === csaat) begin
            `uvm_fatal(`gfn, {"CSB still low since last data sent", $sformatf("There's been %0d half SCK cycles",num_times)})
          end
        end
        begin
          int max_scks_edges = 2;
          repeat(max_scks_edges) @(cfg.m_spi_agent_cfg.vif.sck);
          wait (csaat == 0);
          `uvm_fatal(`gfn, $sformatf("%m - Clock kept ticking"))
        end
        begin
          wait (cfg.m_spi_agent_cfg.vif.csb[0] === 1);
        end
      join_any
      disable fork;
    end join
  endtask

  virtual task update_configopts(spi_host_configopts_t next_spi_configopts);
    if (!initialise_configopts && cfg.m_spi_agent_cfg.vif.csb[0] === 0) begin
      @(cfg.m_spi_agent_cfg.vif.csb[0]);
      cfg.clk_rst_vif.wait_clks(1);
    end
    initialise_configopts = 0;
    curr_spi_configopts = next_spi_configopts;
    spi_clk_half_period = (curr_spi_configopts.clkdiv + 1) * cfg.clk_rst_vif.clk_period_ps;
  endtask

  // Callback methods implementation: Register Write
  virtual function void reg_write(string name, uvm_reg_data_t value);
    `uvm_info(`gfn, $sformatf("Reg Write callback: %s = 0x%0h", name, value), UVM_HIGH)
    case (name)
      "control": begin
        spi_ctrl_reg.spien  = get_field_val(ral.control.spien, value);
        spi_ctrl_reg.sw_rst = get_field_val(ral.control.sw_rst, value);
        if (spi_ctrl_reg.sw_rst) begin
          `uvm_info(`gfn, "SW reset detected", UVM_LOW)
          ->event_sw_rst;
          reset();
        end
      end
      "configopts": begin
        spi_configopts.cpol     = get_field_val(ral.configopts.cpol, value);
        spi_configopts.cpha     = get_field_val(ral.configopts.cpha, value);
        spi_configopts.fullcyc  = get_field_val(ral.configopts.fullcyc, value);
        spi_configopts.csnlead  = get_field_val(ral.configopts.csnlead, value);
        spi_configopts.csntrail = get_field_val(ral.configopts.csntrail, value);
        spi_configopts.csnidle  = get_field_val(ral.configopts.csnidle, value);
        spi_configopts.clkdiv   = get_field_val(ral.configopts.clkdiv, value);
        
        fork
          update_configopts(spi_configopts);
        join_none
      end
      "command": begin
        spi_cmd_reg.direction = spi_dir_e'(get_field_val(ral.command.direction, value));
        spi_cmd_reg.mode      = spi_mode_e'(get_field_val(ral.command.speed, value));
        spi_cmd_reg.csaat     = get_field_val(ral.command.csaat, value);
        spi_cmd_reg.len       = get_field_val(ral.command.len, value);

        host_wr_segment.command_reg.len       = spi_cmd_reg.len;
        host_wr_segment.command_reg.direction = spi_cmd_reg.direction;
        host_wr_segment.command_reg.mode      = spi_cmd_reg.mode;
        host_wr_segment.command_reg.csaat     = spi_cmd_reg.csaat;
        
        if (spi_cmd_reg.direction inside {RxOnly, Bidir}) begin
          // push expected RX segment
          spi_segment_item rd_segment;
          `downcast(rd_segment, host_wr_segment.clone());
          read_segment_q.push_back(rd_segment);
        end

        begin
          spi_segment_item wr_segment;
          `downcast(wr_segment, host_wr_segment.clone());
          if (cfg.tx_stall_check) commit_exp_txn_at_txfifo_write = 1'b1;
          else begin
            write_segment_q.push_back(wr_segment);
            `uvm_info(`gfn, $sformatf("Pushed wr_segment: \n%s onto 'write_segment_q'", wr_segment.convert2string()), UVM_DEBUG)
            host_wr_segment = spi_segment_item::type_id::create("host_wr_segment");
          end
        end
        if (cfg.en_cov) begin
          cov.duplex_cg.sample(spi_cmd_reg.direction);
          cov.command_cg.sample(spi_cmd_reg);
          cov.command_segment_cg.sample(spi_cmd_reg);
        end
      end
      "intr_enable": begin
        spi_intr_enable_reg.spi_event  = bit'(get_field_val(ral.intr_enable.spi_event, value));
        spi_intr_enable_reg.error      = bit'(get_field_val(ral.intr_enable.error, value));
      end
      "intr_test": begin
        spi_intr_test_reg.spi_event  = bit'(get_field_val(ral.intr_test.spi_event, value));
        spi_intr_test_reg.error      = bit'(get_field_val(ral.intr_test.error, value));
        if (cfg.en_cov) begin
          bit [31:0] intr_en = `gmv(ral.intr_enable);
          bit [NumSpiHostIntr-1:0] intr_exp = value | `gmv(ral.intr_state);
          void'(ral.intr_state.predict(.value(intr_exp), .kind(UVM_PREDICT_DIRECT)));
          // TODO: re-enable when interrupt covergroups are added to cov class
          // foreach (intr_exp[i]) begin
          //   cov.intr_test_cg.sample(i, value[i], intr_en[i], intr_exp[i]);
          // end
        end
      end
      "csid": begin
        spi_ctrl_reg.csid = value;
        if (cfg.en_cov) cov.csid_cg.sample(spi_ctrl_reg);
      end
      "error_enable": begin
        spi_error_enable_reg.csidinval = bit'(get_field_val(ral.error_enable.csidinval, value));
        spi_error_enable_reg.cmdinval  = bit'(get_field_val(ral.error_enable.cmdinval, value));
        spi_error_enable_reg.underflow = bit'(get_field_val(ral.error_enable.underflow, value));
        spi_error_enable_reg.overflow  = bit'(get_field_val(ral.error_enable.overflow, value));
        spi_error_enable_reg.cmdbusy   = bit'(get_field_val(ral.error_enable.cmdbusy, value));
        if (cfg.en_cov) cov.error_en_cg.sample(spi_error_enable_reg);
      end
      "event_enable": begin
        spi_event_enable_reg.idle      = bit'(get_field_val(ral.event_enable.idle, value));
        spi_event_enable_reg.ready     = bit'(get_field_val(ral.event_enable.ready, value));
        spi_event_enable_reg.txwm      = bit'(get_field_val(ral.event_enable.txwm, value));
        spi_event_enable_reg.rxwm      = bit'(get_field_val(ral.event_enable.rxwm, value));
        spi_event_enable_reg.txempty   = bit'(get_field_val(ral.event_enable.txempty, value));
        spi_event_enable_reg.rxfull    = bit'(get_field_val(ral.event_enable.rxfull, value));
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
         if (cfg.en_cov) begin
           bit [31:0]               intr_en  = `gmv(ral.intr_enable);
           bit [NumSpiHostIntr-1:0] intr_exp = `gmv(ral.intr_state);
           // TODO: re-enable when interrupt covergroups are added to cov class
           // foreach (intr_exp[i]) begin
           //   cov.intr_cg.sample(i, intr_en[i], value);
           //   cov.intr_pins_cg.sample(i, cfg.intr_vif.pins[i]);
           // end
         end
       end
      "error_status": begin
        spi_error_status_reg.accessinval = bit'(get_field_val(ral.error_status.accessinval, value));
        spi_error_status_reg.csidinval   = bit'(get_field_val(ral.error_status.csidinval, value));
        spi_error_status_reg.cmdinval    = bit'(get_field_val(ral.error_status.cmdinval, value));
        spi_error_status_reg.underflow   = bit'(get_field_val(ral.error_status.underflow, value));
        spi_error_status_reg.overflow    = bit'(get_field_val(ral.error_status.overflow, value));
        spi_error_status_reg.cmdbusy     = bit'(get_field_val(ral.error_status.cmdbusy, value));
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
        spi_status_reg.rx_wm       = get_field_val(ral.status.rxwm, value);
        spi_status_reg.byteorder   = get_field_val(ral.status.byteorder, value);
        if (cfg.en_cov) cov.status_cg.sample(spi_status_reg);
      end
    endcase
  endfunction

  // Callback methods implementation: Memory Write
  virtual function void mem_write(string name, uvm_reg_addr_t offset, uvm_reg_data_t value, uvm_reg_byte_en_t byte_en);
    `uvm_info(`gfn, $sformatf("Mem Write callback: %s [offset 0x%0h] = 0x%0h (be: 0x%0h)", name, offset, value, byte_en), UVM_HIGH)
    if (name == "txdata") begin
      bit [7:0] bytes[4] = {<< 8{value}};
      
      if (cfg.en_cov) begin
        spi_host_status_t status;
        status = spi_host_status_t'(ral.status.get_mirrored_value());
        cov.tx_fifo_overflow_cg.sample(status);
      end

      foreach (bytes[i]) begin
        if (byte_en[i]) begin
          host_wr_segment.spi_data.push_back(bytes[i]);
          `uvm_info(`gfn, $sformatf("Write to TXFIFO: 0x%0x", bytes[i]), UVM_DEBUG)
        end
      end

      if (commit_exp_txn_at_txfifo_write) begin
        spi_segment_item wr_segment;
        commit_exp_txn_at_txfifo_write = 1'b0;
        `downcast(wr_segment, host_wr_segment.clone());
        `uvm_info(`gfn, $sformatf("Pushed segment:\n%s \nonto 'write_segment_q'", wr_segment.convert2string), UVM_DEBUG)
        write_segment_q.push_back(wr_segment);
        host_wr_segment = spi_segment_item::type_id::create("host_wr_segment");
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
        status = spi_host_status_t'(ral.status.get_mirrored_value());
        cov.rx_fifo_underflow_cg.sample(status);
      end

      foreach (bytes[i]) begin
        rx_data_q.push_back(bytes[i]);
        `uvm_info(`gfn, $sformatf("Read from RXFIFO: 0x%0x", bytes[i]), UVM_DEBUG)
      end
    end
  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    plain_data_fifo.flush();
    write_segment_q.delete();
    read_segment_q.delete();
    rx_data_q.delete();
    host_wr_segment = spi_segment_item::type_id::create("host_wr_segment");
    host_rd_segment = spi_segment_item::type_id::create("host_rd_segment");
    initialise_configopts = 1;
  endfunction : reset

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    if (in_tx_seg_cnt != checked_tx_seg_cnt)
      `uvm_fatal(`gfn, $sformatf("Didn't check all segments - expected %0d actual %0d", in_tx_seg_cnt, checked_tx_seg_cnt))

    `DV_EOT_PRINT_Q_CONTENTS(spi_segment_item, write_segment_q)
    `DV_EOT_PRINT_Q_CONTENTS(spi_segment_item, read_segment_q)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(spi_item, plain_data_fifo)
    if ((rx_data_q.size() != 0))
      `uvm_fatal(`gfn, $sformatf("ERROR - RX FIFO in DUT still has data to be read! (rx_data_q = %0d)", rx_data_q.size()))
  endfunction : check_phase

endclass : spi_host_scoreboard
