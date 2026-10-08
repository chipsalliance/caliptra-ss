// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_common_vseq extends uart_base_vseq;
  `uvm_object_utils(uart_common_vseq)

  string common_seq_type;

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task run_intr_test_vseq(int num_times = 1);
    import dv_utils_pkg::interrupt_t;
    dv_base_reg all_csrs[$];
    dv_base_reg intr_csrs[$];
    dv_base_reg intr_test_csrs[$];

    foreach (cfg.ral_models[i]) begin
      cfg.ral_models[i].get_dv_base_regs(all_csrs);
    end

    foreach (all_csrs[i]) begin
      string csr_name = all_csrs[i].get_name();
      if (csr_name inside {"intr_test", "intr_enable", "intr_state"}) begin
        intr_csrs.push_back(ral.get_dv_base_reg_by_name(csr_name));
      end
      if (csr_name == "intr_test") begin
        intr_test_csrs.push_back(ral.get_dv_base_reg_by_name(csr_name));
      end
    end

    foreach (intr_test_csrs[i]) begin
      csr_wr(.ptr(intr_test_csrs[i]), .value(0));
      void'(intr_test_csrs[i].predict(0));
    end
    csr_wr(.ptr(ral.intr_state), .value((1 << NumUartIntr) - 1));
    void'(ral.intr_state.predict(ral.intr_state.get_reset()));

    num_times = num_times * intr_csrs.size();
    for (int trans = 1; trans <= num_times; trans++) begin
      `uvm_info(`gfn, $sformatf("Running intr test iteration %0d/%0d", trans, num_times), UVM_LOW)
      intr_csrs.shuffle();
      foreach (intr_csrs[i]) begin
        uvm_reg_data_t data = $urandom();
        `uvm_info(`gfn, $sformatf("Write %s: 0x%0h", intr_csrs[i].`gfn, data), UVM_MEDIUM)
        csr_wr(.ptr(intr_csrs[i]), .value(data));
        if (intr_csrs[i].get_name() == "intr_test") begin
          uvm_reg_data_t ro_mask   = ral.intr_state.get_ro_mask();
          uvm_reg_data_t reg_mask  = ral.intr_state.get_reg_mask();
          uvm_reg_data_t cur_state = ral.intr_state.get_mirrored_value();
          void'(ral.intr_state.predict((cur_state | (data & ~ro_mask)) & reg_mask));
          void'(intr_csrs[i].predict(0));
        end else if (intr_csrs[i].get_name() == "intr_state") begin
          uvm_reg_data_t ro_mask   = ral.intr_state.get_ro_mask();
          uvm_reg_data_t reg_mask  = ral.intr_state.get_reg_mask();
          uvm_reg_data_t cur_state = ral.intr_state.get_mirrored_value();
          void'(ral.intr_state.predict((cur_state & ~(data & ~ro_mask)) & reg_mask));
        end else if (intr_csrs[i].get_name() == "intr_enable") begin
          void'(ral.intr_enable.predict(data & ral.intr_enable.get_reg_mask()));
        end
        if (cfg.under_reset) break;
      end

      intr_csrs.shuffle();
      foreach (intr_csrs[i]) begin
        uvm_reg_data_t exp_val = `gmv(intr_csrs[i]);
        uvm_reg_data_t act_val;
        interrupt_t irq_ro_mask = '0;

        if (intr_csrs[i].get_name() == "intr_state") begin
          irq_ro_mask = intr_csrs[i].get_ro_mask();
        end
        exp_val &= ~irq_ro_mask;
        csr_rd(.ptr(intr_csrs[i]), .value(act_val));
        act_val &= ~irq_ro_mask;
        if (cfg.under_reset) break;
        `DV_CHECK_EQ(exp_val, act_val, {"when reading the intr CSR ", intr_csrs[i].get_full_name()})
        if (intr_csrs[i].get_name() == "intr_state") begin
          interrupt_t exp_intr_pin = intr_csrs[i].get_intr_pins_exp_value();
          interrupt_t act_intr_pin = cfg.intr_vif.sample();
          act_intr_pin &= interrupt_t'((1 << cfg.num_interrupts) - 1);
          `DV_CHECK_CASE_EQ(exp_intr_pin, act_intr_pin)
        end
      end
    end
    foreach (intr_test_csrs[i]) begin
      csr_wr(.ptr(intr_test_csrs[i]), .value(0));
      void'(intr_test_csrs[i].predict(0));
    end
    csr_wr(.ptr(ral.intr_state), .value((1 << NumUartIntr) - 1));
    void'(ral.intr_state.predict(ral.intr_state.get_reset()));
  endtask

  virtual task run_same_csr_outstanding_vseq(int num_times = 1);
    csr_test_type_e csr_test_type = CsrRwTest;
    for (int trans = 1; trans <= num_times; trans++) begin
      `uvm_info(`gfn, $sformatf("Running same CSR outstanding test iteration %0d/%0d",
                                 trans, num_times), UVM_LOW)
      if (trans != 1 && $urandom_range(0, 1)) dut_init();
      foreach (cfg.ral_models[ral_name]) begin
        dv_base_reg csrs[$];
        cfg.ral_models[ral_name].get_dv_base_regs(csrs);
        csrs.shuffle();
        foreach (csrs[i]) begin
          uvm_reg_data_t exp_data = csrs[i].get_mirrored_value();
          uvm_reg_data_t rd_data, wr_data, rd_mask, wr_mask;
          csr_excl_item  csr_excl = get_excl_item(csrs[i]);
          rd_mask = get_mask_excl_fields(csrs[i], CsrExclWriteCheck, csr_test_type);
          wr_mask = get_mask_excl_fields(csrs[i], CsrExclWrite, csr_test_type);

          repeat ($urandom_range(2, 20)) begin
            if (cfg.under_reset) break;
            if ($urandom_range(0, 1) &&
                !csr_excl.is_excl(csrs[i], CsrExclWriteCheck, csr_test_type)) begin
              csr_rd_check(.ptr(csrs[i]), .compare_vs_ral(1), .compare_mask(rd_mask));
            end
            if ($urandom_range(0, 1) &&
                !csr_excl.is_excl(csrs[i], CsrExclWrite, csr_test_type)) begin
              `DV_CHECK_STD_RANDOMIZE_FATAL(wr_data)
              wr_data &= wr_mask;
              csr_wr(.ptr(csrs[i]), .value(wr_data));
              void'(csrs[i].predict(.value(wr_data), .kind(UVM_PREDICT_WRITE)));
              exp_data = csrs[i].get_mirrored_value();
            end
          end
          csr_utils_pkg::wait_no_outstanding_access();
        end
      end
    end
  endtask

  virtual task run_csr_mem_rw_with_rand_reset_vseq(int num_times = 1);
    for (int i = 1; i <= num_times; i++) begin
      `uvm_info(`gfn, $sformatf("Running csr_mem_rw_with_rand_reset iteration %0d/%0d", i, num_times), UVM_LOW)
      run_csr_vseq(.csr_test_type("hw_reset"), .do_rand_wr_and_reset(1));
    end
  endtask

  virtual task body();
    if ($test$plusargs("run_sec_cm_fi") || $test$plusargs("run_sec_cm")) begin
      uart_sec_cm_vseq sec_cm_vseq;
      `uvm_create_on(sec_cm_vseq, p_sequencer)
      `DV_CHECK_RANDOMIZE_FATAL(sec_cm_vseq)
      sec_cm_vseq.start(p_sequencer);
    end else begin
      cfg.m_uart_agent_cfg.en_tx_checks = 1'b0;
      cfg.m_uart_agent_cfg.en_rx_checks = 1'b0;
      if (ral.default_map.get_adapter() != null) begin
        ral.default_map.get_adapter().supports_byte_enable = 1;
      end
      ral.default_map.set_auto_predict(1);
      if (common_seq_type == "") void'($value$plusargs("run_%0s", common_seq_type));
      case (common_seq_type)
        "intr_test":                  run_intr_test_vseq(num_trans);
        "same_csr_outstanding":       run_same_csr_outstanding_vseq(num_trans);
        "csr_mem_rw_with_rand_reset": run_csr_mem_rw_with_rand_reset_vseq(num_trans);
        default:                      run_csr_vseq_wrapper(num_trans);
      endcase
    end
  endtask : body

endclass
