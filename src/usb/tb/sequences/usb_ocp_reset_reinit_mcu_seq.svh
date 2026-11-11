// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_reset_reinit_mcu_seq extends usb_ocp_base_mcu_seq;
  `uvm_object_utils(usb_ocp_reset_reinit_mcu_seq)
  usb_ocp_reset_model reset_model;
  usb_ocp_scoreboard scoreboard;
  bit reset_serviced;

  function new(string name = "usb_ocp_reset_reinit_mcu_seq");
    super.new(name);
  endfunction

  virtual task ocp_do_check_reset_indication(logic [31:0] command);
    if (reset_model == null || scoreboard == null)
      `uvm_fatal("OCP_RESET_MCU", "Missing reset service context")
    if (!reset_model.cfg.armed || !reset_model.cfg.ocp_check_recovery_affected() ||
        reset_serviced) return;
    if ((command & ocp_get_mask("DEVCMDSTAT","DRES_C")) !==
                   ocp_get_mask("DEVCMDSTAT","DRES_C"))
      `uvm_fatal("OCP_RESET_MCU", "Abort request lacks actual owned hardware reset indication")
    reset_serviced = 1;
    reset_model.cfg.abort_requested = 1;
    while (!reset_model.cfg.caliptra_quiescent || !reset_model.cfg.retention_complete) begin
      if ($time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_MCU", "Caliptra did not acknowledge accounted abort/quiescence")
      #1us;
    end
    // The sole MCU recovery-write exception follows the acknowledged handoff.
    // Normal USB CSR/ECL reset processing resumes through the inherited owner.
    ral_write32("RESET_DEVICE_STATUS_1",
      p_sequencer.reg_model.combo.recovery.DEVICE_STATUS_1,0);
    ral_write32("RESET_DEVICE_STATUS_0",
      p_sequencer.reg_model.combo.recovery.DEVICE_STATUS_0,
      (32'(OCP_REC_REASON_FORCED_RECOVERY)<<16) | OCP_DEVICE_STATUS_RECOVERY_MODE);
    while (scoreboard.busy || scoreboard.deferred_axi.size() != 0 ||
           reset_model.reinit_writes != 2) begin
      if ($time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_MCU", "MCU status writes lack completed accepted-AXI evidence")
      #1us;
    end
    reset_model.cfg.mcu_reinitialized = 1;
  endtask
endclass
