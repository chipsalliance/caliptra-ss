// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergroups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

class spi_host_env_cov extends dv_base_env_cov #(.CFG_T(spi_host_env_cfg));
  `uvm_component_utils(spi_host_env_cov)

  // Sample this covergroup upon writes to the TXFIFO register window.
  covergroup tx_fifo_overflow_cg with function sample(spi_host_status_t spi_status_reg);
    tx_fifo_overflow_txfull_cp : coverpoint spi_status_reg.txfull {
      // Trying to write to TXFIFO while status.txfull = 1'b1 indicates an overflow event.
      bins try_overflow = {1};
    }
  endgroup : tx_fifo_overflow_cg

  // Sample this covergroup upon reads from the RXFIFO register window.
  covergroup rx_fifo_underflow_cg with function sample(spi_host_status_t spi_status_reg);
    rx_fifo_underflow_rxempty_cp : coverpoint spi_status_reg.rxempty {
      // Trying to read from RXFIFO while status.rxempty = 1'b1 indicates an underflow event.
      bins try_underflow = {1};
    }
  endgroup : rx_fifo_underflow_cg

  covergroup config_opts_cg with function sample(spi_host_configopts_t spi_configopts);
    cpol_cp : coverpoint spi_configopts.cpol{ bins cpol[] = {[0:1]}; }
    cpha_cp : coverpoint spi_configopts.cpha{ bins cpha[] = {[0:1]}; }
    fullcyc_cp : coverpoint spi_configopts.fullcyc{
    bins fullcyc[] = {[0:1]};
    }
    csnlead_cp : coverpoint spi_configopts.csnlead{
      bins zero = {0};
      bins low = {[1:5]};
      bins mid = {[6:10]};
      bins high = {[11:15]};
    }
    csnidle_cp : coverpoint spi_configopts.csnidle{
      bins zero = {0};
      bins low = {[1:5]};
      bins mid = {[6:10]};
      bins high = {[11:15]};
    }
    clkdiv_cp : coverpoint spi_configopts.clkdiv{
      bins clk_div_zero = {0};
      bins clk_div_small[4] = {[16'h1:16'h000f]};
      bins clk_divm_bottom_eight[5] = {[16'h0010:16'h00fe]};
      bins clk_divm_upper_eight[5] = {[16'h00ff:16'hfffe]};
      bins clk_divm_max = {16'hffff};
    }
    csntrail_cp : coverpoint spi_configopts.csntrail{
      bins zero = {0};
      bins low = {[1:5]};
      bins mid = {[6:10]};
      bins high = {[11:15]};
    }
    cpol_cpha_cross :  cross cpol_cp, cpha_cp;
    csnlead_csnidle_csntrail_cross: cross csnlead_cp, csnidle_cp, csntrail_cp;
  endgroup

  covergroup unaligned_data_cg with function sample(bit [3:0] mask);
    unaligned_data_cp: coverpoint mask{ bins mask = {[0:15]}; }
  endgroup

  covergroup duplex_cg with function sample(spi_dir_e  direction);
    duplex_cp : coverpoint direction{ ignore_bins unsupported_dir = {None}; }
  endgroup

  covergroup control_cg with function sample(spi_host_ctrl_t spi_ctrl_reg, bit active);
    tx_watermark_cp : coverpoint spi_ctrl_reg.tx_watermark{
      bins zero = {0};
      bins low  = {[1:15]};
      bins mid  = {[16:47]};
      bins high = {[48:SPI_HOST_TX_DEPTH]};
      ignore_bins invalid = {[SPI_HOST_TX_DEPTH+1:$]};
    }
    rx_watermark_cp : coverpoint spi_ctrl_reg.rx_watermark{
      bins zero = {0};
      bins low  = {[1:15]};
      bins mid  = {[16:47]};
      bins high = {[48:SPI_HOST_RX_DEPTH]};
      ignore_bins invalid = {[SPI_HOST_RX_DEPTH+1:$]};
    }
    spien_cp : coverpoint spi_ctrl_reg.spien { bins spien = {1}; }
    output_en_cp : coverpoint spi_ctrl_reg.output_en { bins output_en = {1}; }
    sw_rst_cp : coverpoint spi_ctrl_reg.sw_rst { bins sw_rst = {1}; }
    sw_rst_active_cross : cross sw_rst_cp, active;
  endgroup

  covergroup status_cg with function sample(spi_host_status_t spi_status_reg);
    ready_cp : coverpoint spi_status_reg.ready;
    active_cp : coverpoint spi_status_reg.active;
    txfull_cp : coverpoint spi_status_reg.txfull;
    txempty_cp : coverpoint spi_status_reg.txempty;
    txstall_cp : coverpoint spi_status_reg.txstall;
    tx_wm_cp : coverpoint spi_status_reg.tx_wm;
    rxfull_cp : coverpoint spi_status_reg.rxfull;
    rxempty_cp : coverpoint spi_status_reg.rxempty;
    rxstall_cp : coverpoint spi_status_reg.rxstall;
    byteorder_cp : coverpoint spi_status_reg.byteorder {
      bins byteorder = {SPI_HOST_BYTEORDER};
      ignore_bins invalid = {~SPI_HOST_BYTEORDER};
    }
    rx_wm_cp : coverpoint spi_status_reg.rx_wm;
    cmd_qd_cp : coverpoint spi_status_reg.cmd_qd {
      bins empty     = {0};
      bins partial[] = {[1:SPI_HOST_CMD_DEPTH-1]};
      bins full      = {SPI_HOST_CMD_DEPTH};
      ignore_bins invalid = {[SPI_HOST_CMD_DEPTH+1:$]};
    }
    rx_qd_cp : coverpoint spi_status_reg.rx_qd {
      bins empty = {0};
      bins low   = {[1:16]};
      bins mid   = {[17:48]};
      bins high  = {[49:SPI_HOST_RX_DEPTH-1]};
      bins full  = {SPI_HOST_RX_DEPTH};
      ignore_bins invalid = {[SPI_HOST_RX_DEPTH+1:$]};
    }
    tx_qd_cp : coverpoint spi_status_reg.tx_qd {
      bins empty = {0};
      bins low   = {[1:16]};
      bins mid   = {[17:48]};
      bins high  = {[49:SPI_HOST_TX_DEPTH-1]};
      bins full  = {SPI_HOST_TX_DEPTH};
      ignore_bins invalid = {[SPI_HOST_TX_DEPTH+1:$]};
    }
  endgroup

  covergroup csid_cg with function sample(spi_host_ctrl_t spi_ctrl_reg);
    csid_cp : coverpoint spi_ctrl_reg.csid {
      bins csids = {[0:SPI_HOST_NUM_CS-1]};
    }
  endgroup

  covergroup command_cg with function sample(spi_host_command_t spi_cmd_reg);
    direction_cp : coverpoint spi_cmd_reg.direction;
    mode_cp : coverpoint spi_cmd_reg.mode {
      ignore_bins unsupported_mode = {RsvdSpd};
      }
    csaat_cp : coverpoint spi_cmd_reg.csaat;
    len_cp : coverpoint spi_cmd_reg.len{
      bins lenl[5] = {[1:3]};
      bins lenh[10] = {[4:(2**SPI_HOST_COMMAND_LEN_SIZE_BITS)-1]};
      }
    direction_mode_cross: cross  direction_cp, mode_cp;
    csaat_mode_cross: cross csaat_cp, mode_cp;
  endgroup

  covergroup error_en_cg with function sample(spi_host_error_enable_t spi_error_enable_reg);
    ere_csidinval_cp : coverpoint spi_error_enable_reg.csidinval;
    ere_cmdinval_cp : coverpoint spi_error_enable_reg.cmdinval;
    ere_underflow_cp : coverpoint spi_error_enable_reg.underflow;
    ere_overflow_cp : coverpoint spi_error_enable_reg.overflow;
    ere_cmdbusy_cp : coverpoint spi_error_enable_reg.cmdbusy;
  endgroup

  covergroup error_status_cg with function sample(spi_host_error_status_t spi_error_status_reg,
                                                  spi_host_error_enable_t spi_error_enable_reg);
    es_accessinval_cp : coverpoint spi_error_status_reg.accessinval;
    es_csidinval_cp : coverpoint spi_error_status_reg.csidinval;
    es_cmdinval_cp : coverpoint spi_error_status_reg.cmdinval;
    es_underflow_cp : coverpoint spi_error_status_reg.underflow;
    es_overflow_cp : coverpoint spi_error_status_reg.overflow;
    es_cmdbusy_cp : coverpoint spi_error_status_reg.cmdbusy;
    ere_csidinval_cp : coverpoint spi_error_enable_reg.csidinval;
    ere_cmdinval_cp : coverpoint spi_error_enable_reg.cmdinval;
    ere_underflow_cp : coverpoint spi_error_enable_reg.underflow;
    ere_overflow_cp : coverpoint spi_error_enable_reg.overflow;
    ere_cmdbusy_cp : coverpoint spi_error_enable_reg.cmdbusy;
    err_csidinval_cross: cross ere_csidinval_cp, es_csidinval_cp;
    err_cmdinval_cross: cross ere_cmdinval_cp, es_cmdinval_cp;
    err_underflow_cross: cross ere_underflow_cp, es_underflow_cp;
    err_overflow_cross: cross ere_overflow_cp, es_overflow_cp;
    err_cmdbusy_cross: cross ere_cmdbusy_cp, es_cmdbusy_cp;
  endgroup

  covergroup event_en_cg with function sample(spi_host_event_enable_t spi_event_enable_reg);
    idle_cp : coverpoint spi_event_enable_reg.idle;
    ready_cp : coverpoint spi_event_enable_reg.ready;
    txwm_cp : coverpoint spi_event_enable_reg.txwm;
    rxwm_cp : coverpoint spi_event_enable_reg.rxwm;
    txempty_cp : coverpoint spi_event_enable_reg.txempty;
    rxfull_cp : coverpoint spi_event_enable_reg.rxfull;
  endgroup

  covergroup command_segment_cg with function sample(spi_host_command_t spi_cmd_reg);

    csaat_cp: coverpoint spi_cmd_reg.csaat;

    speed_cp : coverpoint spi_cmd_reg.mode{
      ignore_bins unsupported_speed = {RsvdSpd};
    }
    speed_trans_cp : coverpoint spi_cmd_reg.mode {
      // Creates a bin for each of the possible transitions
      bins Any2Any[] = ([Standard:Quad] => [Standard:Quad]);
    }
    direction_cp: coverpoint spi_cmd_reg.direction;
    direction_transition_cp: coverpoint spi_cmd_reg.direction{
      // Creates a bin for each of the possible transitions
      bins Any2Any[] = ([None:Bidir] => [None:Bidir]);
    }
    len_cp: coverpoint spi_cmd_reg.len{
      bins zero = {0};
      bins one = {1};
      bins middle_range_val = {[2:2**SPI_HOST_COMMAND_LEN_SIZE_BITS - 2]};
      bins max_val = { 2**SPI_HOST_COMMAND_LEN_SIZE_BITS - 1 };
    }
    //XCOV
    speedXdirectionXcsaat_cp: cross speed_cp, direction_cp, csaat_cp;

  endgroup // command_segment_cg

  // Collect coverage that multiple SPI endpoints are run with different config opts
  covergroup different_ch_settings_cg with function sample(bit [31:0] csid, spi_host_configopts_t spi_configopts);
    csid_cp : coverpoint csid { bins csids[] = {[0:SPI_HOST_NUM_CS-1]}; }
    cpol_cp : coverpoint spi_configopts.cpol { bins cpol[] = {[0:1]}; }
    cpha_cp : coverpoint spi_configopts.cpha { bins cpha[] = {[0:1]}; }
    fullcyc_cp : coverpoint spi_configopts.fullcyc { bins fullcyc[] = {[0:1]}; }
    clkdiv_cp : coverpoint spi_configopts.clkdiv {
      bins clk_div_zero = {0};
      bins clk_div_low = {[1:16'h00fe]};
      bins clk_div_high = {[16'h00ff:16'hfffe]};
      bins clk_div_max = {16'hffff};
    }
    csid_config_cross: cross csid_cp, cpol_cp, cpha_cp;
  endgroup

  // Check that DUT only transmits what is in command even if more segments are in TX FIFO
  covergroup num_segment_cg with function sample(int unsigned num_segments, int unsigned cmd_len, bit extra_data_in_fifo);
    num_segments_cp : coverpoint num_segments {
      bins single_seg = {1};
      bins few_segs   = {[2:5]};
      bins many_segs  = {[6:20]};
    }
    cmd_len_cp : coverpoint cmd_len {
      bins small_len = {[0:3]};
      bins med_len   = {[4:31]};
      bins max_len   = {[32:$]};
    }
    extra_fifo_cp : coverpoint extra_data_in_fifo {
      bins no_extra  = {0};
      bins has_extra = {1};
    }
    num_seg_extra_cross : cross num_segments_cp, extra_fifo_cp;
  endgroup

  // Multi-segment speed transitions (Standard -> Dual -> Quad)
  covergroup segment_speed_cg with function sample(spi_mode_e prev_speed, spi_mode_e curr_speed);
    prev_speed_cp : coverpoint prev_speed {
      ignore_bins unsupported_prev = {RsvdSpd};
    }
    curr_speed_cp : coverpoint curr_speed {
      ignore_bins unsupported_curr = {RsvdSpd};
    }
    speed_transition_cross : cross prev_speed_cp, curr_speed_cp;
  endgroup

  // Passthrough mode coverage (only active when SPI_HOST_NUM_CS == 1)
  covergroup passthrough_cg with function sample(bit passthrough_en, bit normal_txn_active, bit passthrough_data_driven);
    option.weight = (SPI_HOST_NUM_CS == 1) ? 1 : 0;
    passthrough_en_cp : coverpoint passthrough_en { bins en[] = {0, 1}; }
    txn_active_cp     : coverpoint normal_txn_active { bins active[] = {0, 1}; }
    data_driven_cp    : coverpoint passthrough_data_driven { bins driven[] = {0, 1}; }
    passthrough_active_cross : cross passthrough_en_cp, txn_active_cp;
    passthrough_ignore_cross : cross passthrough_en_cp, data_driven_cp;
  endgroup

  // Interrupt assertion & test coverage
  covergroup intr_test_cg with function sample(int intr_idx, bit test_val, bit en_val, bit exp_val);
    intr_idx_cp : coverpoint intr_idx { bins idx[] = {[0:NumSpiHostIntr-1]}; }
    test_val_cp : coverpoint test_val { bins val[] = {[0:1]}; }
    en_val_cp   : coverpoint en_val { bins val[] = {[0:1]}; }
    exp_val_cp  : coverpoint exp_val { bins val[] = {[0:1]}; }
    intr_test_cross : cross intr_idx_cp, test_val_cp, en_val_cp, exp_val_cp {
      ignore_bins test_val_1_exp_val_0 = binsof(test_val_cp) intersect {1} &&
                                         binsof(exp_val_cp) intersect {0};
    }
  endgroup

  covergroup intr_cg with function sample(int intr_idx, bit en_val, bit state_val);
    intr_idx_cp  : coverpoint intr_idx { bins idx[] = {[0:NumSpiHostIntr-1]}; }
    en_val_cp    : coverpoint en_val { bins val[] = {[0:1]}; }
    state_val_cp : coverpoint state_val { bins val[] = {[0:1]}; }
    intr_cross   : cross intr_idx_cp, en_val_cp, state_val_cp;
  endgroup

  covergroup intr_pins_cg with function sample(int intr_idx, bit pin_val);
    intr_idx_cp : coverpoint intr_idx { bins idx[] = {[0:NumSpiHostIntr-1]}; }
    pin_val_cp  : coverpoint pin_val { bins val[] = {[0:1]}; }
    pin_cross   : cross intr_idx_cp, pin_val_cp;
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);

    tx_fifo_overflow_cg = new();
    rx_fifo_underflow_cg = new();
    config_opts_cg = new();
    unaligned_data_cg = new();
    duplex_cg = new();
    control_cg = new();
    status_cg = new();
    csid_cg = new();
    command_cg = new();
    error_en_cg = new();
    error_status_cg = new();
    event_en_cg = new();
    command_segment_cg = new();
    different_ch_settings_cg = new();
    num_segment_cg = new();
    segment_speed_cg = new();
    passthrough_cg = new();
    intr_test_cg = new();
    intr_cg = new();
    intr_pins_cg = new();
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // [or instantiate covergroups here]
    // Please instantiate sticky_intr_cov array of objects for all interrupts that are sticky
    // See cip_base_env_cov for details
  endfunction

endclass
