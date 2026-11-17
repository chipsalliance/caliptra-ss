// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// --------------------
// Device sequence
// This sequence acts as a reactive SPI device responder when a DUT acts as host.
// Multi-CS aware: tracks the active chip-select via item.csb_sel / cfg.vif.csb.
// --------------------

class spi_device_cmd_rsp_seq extends spi_device_seq;
  `uvm_object_utils(spi_device_cmd_rsp_seq)
  `uvm_object_new

  // read queue
  spi_item rsp_q[$];
  spi_fsm_e spi_state = SpiIdle;

  // state-variables
  spi_cmd_e           cmd;
  int                 byte_cnt   = 0;
  bit [CSB_WIDTH-1:0] active_csb = '0;
  bit                 rsp_queued = 1'b0;

  virtual task body();
    if (cfg.in_reset) wait(!cfg.in_reset);

    fork
      get_req();
      decode_cmd();
      send_rsp(rsp_q);
    join
  endtask : body

  virtual task decode_cmd();
    spi_item item;

    forever begin
      fork begin: iso_fork
        fork
          get_nxt_req(item);
          begin
            wait (&cfg.vif.csb === 1'b1);
            if (spi_state == SpiIdle) begin
              wait (&cfg.vif.csb === 1'b0);
              wait (&cfg.vif.csb === 1'b1);
            end
            spi_state  = SpiIdle;
            byte_cnt   = 0;
            rsp_queued = 1'b0;
            rsp_q.delete();
          end
        join_any
        disable fork;
      end: iso_fork join

      if (&cfg.vif.csb === 1'b1) continue;

      if (item.first_byte) begin
        active_csb = item.csb_sel;
        byte_cnt   = 0;
        rsp_queued = 1'b0;
        cmd        = cmd_check(item.data.pop_front());
        spi_state  = SpiCmd;
      end

      case (spi_state)
        SpiIdle:;
        SpiCmd: begin
          byte_cnt += 1;
          if (byte_cnt == cfg.spi_cmd_width) begin
            byte_cnt  = 0;
            spi_state = SpiData;
            if (cmd inside {ReadStd, ReadDual, ReadQuad} && !rsp_queued) begin
              handle_reads(active_csb);
              rsp_queued = 1'b1;
            end
          end
        end
        SpiData: begin
          case (cmd)
            ReadStd, ReadDual, ReadQuad: begin
              if (!rsp_queued) begin
                handle_reads(active_csb);
                rsp_queued = 1'b1;
              end
            end
            WriteStd, WriteDual, WriteQuad: handle_writes(item);
            AltCmd, CmdOnly:;
            default: `uvm_fatal(`gfn, $sformatf("UNSUPPORTED COMMAND 0x%0h", cmd))
          endcase
        end
        default: `uvm_fatal(`gfn, "BAD STATE")
      endcase
    end
  endtask : decode_cmd

  function void handle_reads(bit [CSB_WIDTH-1:0] cs_sel);
    spi_item rsp = spi_item::type_id::create("rsp");
    spi_item rsp_clone;

    case (cmd)
      ReadStd : cfg.spi_mode = Standard;
      ReadDual: cfg.spi_mode = Dual;
      ReadQuad: cfg.spi_mode = Quad;
      default : cfg.spi_mode = RsvdSpd;
    endcase

    `DV_CHECK_RANDOMIZE_WITH_FATAL(rsp,
      csb_sel == local::cs_sel;
      (cmd == ReadStd)  -> data.size() ==  256;
      (cmd == ReadDual) -> data.size() ==  512;
      (cmd == ReadQuad) -> data.size() == 1024;
      num_lanes == cfg.get_sio_size();)
    `downcast(rsp_clone, rsp.clone())
    rsp_q.push_back(rsp_clone);
  endfunction : handle_reads

  function void handle_writes(spi_item item);
    if (item.data.size() > 0) void'(item.data.pop_front());
  endfunction : handle_writes

  function spi_cmd_e cmd_check(bit [7:0] data);
    spi_cmd_e decoded_cmd;
    if (!$cast(decoded_cmd, data)) decoded_cmd = ReadStd;
    return decoded_cmd;
  endfunction : cmd_check
endclass : spi_device_cmd_rsp_seq
