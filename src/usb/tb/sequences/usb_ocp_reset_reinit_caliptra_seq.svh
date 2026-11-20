// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_reset_reinit_caliptra_seq extends usb_ocp_base_caliptra_seq;
  `uvm_object_utils(usb_ocp_reset_reinit_caliptra_seq)
  usb_ocp_reset_model reset_model;
  usb_ocp_scoreboard scoreboard;
  bit completing_old_batch;

  function new(string name = "usb_ocp_reset_reinit_caliptra_seq");
    super.new(name);
  endfunction

  virtual function bit ocp_check_attempt_abort();
    return reset_model != null && reset_model.cfg.abort_requested &&
           reset_model.cfg.attempt == 0 && !completing_old_batch;
  endfunction

  virtual task ocp_wait_attempt_abort();
    if (reset_model.cfg.attempt == 0 && !completing_old_batch)
      wait (reset_model.cfg.abort_requested);
    else wait (1'b0);
  endtask

  task ocp_poll_check_accounting();
    bit idle;
    do begin
      idle = !scoreboard.busy && scoreboard.deferred_axi.size() == 0 &&
             (scoreboard.model.token == null ||
              reset_model.ocp_check_command_service()) &&
             scoreboard.observer.ocp_check_snapshots_consumed();
      foreach (scoreboard.observer.accepted_axi[key])
        if (scoreboard.observer.accepted_axi[key].manager == 0 &&
            scoreboard.model.recovery_register.exists(
              scoreboard.observer.accepted_axi[key].axi_address)) idle = 0;
      if (!idle) begin
        if ($time >= reset_model.cfg.deadline)
          `uvm_fatal("OCP_RESET_QUIESCENCE", "Accepted recovery AXI did not retire within abort bound")
        #1us;
      end
    end while (!idle);
    if (scoreboard.model.fifo_actual.size() != 0 ||
        scoreboard.model.compared_bytes != scoreboard.model.returned_bytes)
      `uvm_fatal("OCP_RESET_QUIESCENCE", "Returned old image bytes remain unaccounted")
  endtask

  task ocp_do_check_retention_snapshot(bit after_reset, bit command_effects = 0);
    uvm_reg registers[$];
    logic [31:0] value;
    if (after_reset && command_effects)
      `uvm_fatal("OCP_RESET_RETENTION", "Command-effects checkpoint must precede reset")
    if (after_reset) begin
      while (!reset_model.epoch_changed || !reset_model.reset_seen[0] ||
             (reset_model.cfg.scope == usb_ocp_reset_control::BUS && !reset_model.reset_seen[1])) begin
        if ($time >= reset_model.cfg.deadline)
          `uvm_fatal("OCP_RESET_RETENTION", "Pre-firmware snapshot lacks all actual affected reset indications")
        #1us;
      end
    end
    ocp_poll_check_accounting();
    reset_model.sampling = command_effects ? 3 : (after_reset ? 2 : 1);
    if (command_effects)
      reset_model.command_read_floor = scoreboard.observer.next_order;
    p_sequencer.reg_model.combo.recovery.get_registers(registers);
    foreach (registers[i]) begin
      // No destructive FIFO peek and no RAL mirror/reset value oracle.
      if (registers[i].get_name() == "INDIRECT_FIFO_DATA") continue;
      ocp_read_register(registers[i].get_name(),value);
      ocp_poll_check_accounting();
    end
    reset_model.sampling = 0;
    if (command_effects) reset_model.ocp_check_command_checkpoint_complete();
    else if (after_reset) reset_model.ocp_check_retention_complete();
    else reset_model.snapshot_ready = 1;
  endtask

  virtual task ocp_do_check_dma_boundary();
    if (reset_model.cfg.attempt != 0 || reset_model.snapshot_ready ||
        reset_model.cfg.stage != usb_ocp_reset_control::PARTIAL) return;
    while (!reset_model.partial_ready) begin
      if ($time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_BOUNDARY", "Initial partial image checkpoint was not reached")
      #1us;
    end
    if (reset_model.cfg.ocp_check_recovery_affected()) begin
      // This is the existing deliberate pre-DMA boundary, not a hold after
      // a DUT fault. Require actual normal publication before snapshot/reset.
      ocp_poll_dma_ready(0,reset_model.cfg.deadline);
      if (drained_words != 0 || ocp_cfg.recovery_vif.payload_available !== 1'b1)
        `uvm_fatal("OCP_RESET_PUBLICATION", "Normal old publication was not ready at the planned boundary")
    end
    ocp_do_check_retention_snapshot(0);
    if (reset_model.cfg.ocp_check_recovery_affected())
      while (!ocp_check_attempt_abort()) begin
        if ($time >= reset_model.cfg.deadline)
          `uvm_fatal("OCP_RESET_ABORT", "MCU did not request abort after actual reset")
        #1us;
      end
  endtask

  task ocp_do_check_old_published_batch();
    logic [31:0] size_words;
    int unsigned batch_words;
    int unsigned burst_words;
    if (!reset_model.cfg.abort_requested || !reset_model.cfg.retention_complete ||
        drained_words != 0 || completing_old_batch)
      `uvm_fatal("OCP_RESET_PUBLICATION", "Old normal batch completion lacks abort/post-snapshot boundary")
    ocp_read_register("INDIRECT_FIFO_CTRL_1",size_words);
    ocp_poll_check_accounting();
    if ($isunknown(size_words) || size_words <= drained_words || size_words > 1024)
      `uvm_fatal("OCP_RESET_PUBLICATION", "Retained firmware image size cannot authorize the normal old batch")
    batch_words = size_words-drained_words;
    if (batch_words > 64) batch_words = 64;
    if (batch_words != 64 || reset_model.old_accepted != batch_words*4)
      `uvm_fatal("OCP_RESET_PUBLICATION", "Old accepted publication does not match normal firmware batch policy")
    // Abort stays latched and ownership stays with Caliptra. Only this
    // planned already-published completion must not short-circuit the common
    // readiness helper's abort branch; timeout/stop and real readiness remain
    // mandatory. No firmware attempt or subsequent publication runs here.
    completing_old_batch = 1;
    ocp_poll_dma_ready(0,reset_model.cfg.deadline);
    reset_model.ocp_check_begin_old_batch(ocp_cfg.recovery_vif.payload_available);
    while (batch_words != 0) begin
      burst_words = (batch_words > 16) ? 16 : batch_words;
      ocp_do_check_dma_burst(burst_words);
      ocp_poll_check_accounting();
      batch_words -= burst_words;
    end
    ocp_poll_dma_ready(0,reset_model.cfg.deadline,1'b0);
    ocp_poll_check_accounting();
    reset_model.ocp_check_old_batch_complete(ocp_cfg.recovery_vif.payload_available);
    completing_old_batch = 0;
  endtask

  virtual task ocp_do_check_activation_boundary();
    if (reset_model.cfg.attempt != 0 ||
        reset_model.cfg.stage == usb_ocp_reset_control::PARTIAL) return;
    ocp_do_check_retention_snapshot(0);
    while (reset_model.cfg.ocp_check_recovery_affected() ?
           !ocp_check_attempt_abort() : !reset_model.window_open) begin
      if ($time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_ABORT", "Activation checkpoint lacks bounded reset/abort service")
      if (reset_model.command_checkpoint_requested &&
          !reset_model.command_checkpoint_ready)
        ocp_do_check_retention_snapshot(0,1);
      else #1us;
    end
  endtask

  task body();
    logic [31:0] value;
    int unsigned unretired_witness;
    if (reset_model == null || scoreboard == null)
      `uvm_fatal("OCP_RESET_CALIPTRA", "Missing reset coordination/passive checker")
    ocp_do_check_attempt();
    if (reset_model.cfg.ocp_check_recovery_affected()) begin
      if (!ocp_check_attempt_abort())
        `uvm_fatal("OCP_RESET_ABORT", "Old recovery completed instead of servicing MCU abort")
      // Every accepted operation finished normally before this acknowledgement.
      // No sequence kill, whole-core reset, or queue discard is an abort.
      ocp_poll_check_accounting();
      // All registers/indices are sampled before ANY new recovery writer or
      // old DMA completion can mask a reset effect.
      ocp_do_check_retention_snapshot(1);
      if (reset_model.cfg.stage == usb_ocp_reset_control::PARTIAL)
        ocp_do_check_old_published_batch();
      ocp_poll_check_accounting();
      unretired_witness = scoreboard.model.fifo_actual.size();
      foreach (scoreboard.observer.accepted_axi[key])
        if (scoreboard.observer.accepted_axi[key].manager == 0 &&
            scoreboard.model.recovery_register.exists(
              scoreboard.observer.accepted_axi[key].axi_address)) unretired_witness++;
      if (reset_model.cfg.negative == usb_ocp_reset_control::QUIESCENCE) unretired_witness++;
      if (unretired_witness != 0)
        `uvm_error("OCP_RESET_QUIESCENCE", "Quiescence witness contains an unretired accepted-operation operand")
      reset_model.ocp_check_abort_ack();
      reset_model.cfg.caliptra_quiescent = 1;
      while (!reset_model.cfg.mcu_reinitialized) begin
        if ($time >= reset_model.cfg.deadline)
          `uvm_fatal("OCP_RESET_REINIT", "MCU writer handoff deadline")
        #1us;
      end
      reset_model.cfg.attempt = 1;
      ocp_write_register("RECOVERY_CTRL",0);
      // MCU Recovery Mode permits host discovery, but not reuse of old size.
      // Only the observed explicit reset authorizes the zero-size checkpoint.
      while (!reset_model.cfg.fifo_reset_observed) begin
        if ($time >= reset_model.cfg.deadline)
          `uvm_fatal("OCP_RESET_FIFO", "Fresh host did not explicitly reset FIFO")
        #1us;
      end
      ocp_read_register("INDIRECT_FIFO_CTRL_1",value);
      if (value !== 0)
        `uvm_fatal("OCP_RESET_FIFO", "Fresh attempt did not observe reset image size zero")
      ocp_read_register("INDIRECT_FIFO_CTRL_0",value);
      if (value[15:8] !== 0)
        `uvm_fatal("OCP_RESET_FIFO", "FIFO reset did not self-clear at native firmware frontdoor")
      if (ocp_cfg.recovery_vif.payload_available !== 0 ||
          ocp_cfg.recovery_vif.image_activated !== 0)
        `uvm_fatal("OCP_RESET_FIFO", "Explicit FIFO reset left stale DMA/activation indications")
      reset_model.cfg.fresh_zero_observed = 1;
      drained_words = 0;
      ocp_do_check_attempt();
    end
    completed = 1;
    ocp_poll_teardown();
    ocp_cfg.actor_finished[2] = 1;
  endtask
endclass
