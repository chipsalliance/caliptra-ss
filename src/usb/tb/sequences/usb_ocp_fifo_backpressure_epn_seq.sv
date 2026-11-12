// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_fifo_backpressure_epn_seq extends usb_ocp_base_epn_overlap_seq;
  `uvm_object_utils(usb_ocp_fifo_backpressure_epn_seq)
  usb_ocp_fifo_backpressure_epn_checker fifo_checker;
  string peer = "DEV0";

  function new(string name = "usb_ocp_fifo_backpressure_epn_seq");
    super.new(name);
  endfunction

  virtual function usb_ocp_base_host_seq ocp_prepare_host();
    usb_ocp_fifo_backpressure_epn_host_seq host;
    host = usb_ocp_fifo_backpressure_epn_host_seq::type_id::create("host");
    host.fifo_checker = fifo_checker;
    host.scoreboard = scoreboard;
    host.epn_device = epn_device;
    return host;
  endfunction

  virtual function usb_ocp_base_caliptra_seq ocp_prepare_caliptra();
    usb_ocp_fifo_backpressure_epn_caliptra_seq caliptra;
    caliptra = usb_ocp_fifo_backpressure_epn_caliptra_seq::type_id::create("caliptra");
    caliptra.fifo_checker = fifo_checker;
    return caliptra;
  endfunction

  task body();
    bit armed;
    bit full;
    if (!uvm_config_db#(usb_ocp_scoreboard)::get(p_sequencer,"","ocp_scoreboard",scoreboard) ||
        !$cast(fifo_checker,scoreboard))
      `uvm_fatal("OCP_FIFO_EPN_GUARD", "FIFO EPN requires its owned passive checker")
    if (ocp_cfg.full_speed || ocp_cfg.recovery_vif == null ||
        scoreboard.l2_model != null || scoreboard.reset_model != null ||
        scoreboard.model.stall_model != null || scoreboard.model.require_dev0_ep0_replacement ||
        scoreboard.model.require_dev1_ep0_overlap || scoreboard.model.require_mixed_epn ||
        $test$plusargs("usb_ocp_control_zlp_canary") ||
        scoreboard.negative_payload || scoreboard.negative_activation || scoreboard.negative_dma ||
        scoreboard.negative_overlap || scoreboard.negative_replacement ||
        scoreboard.negative_abort_prefix || scoreboard.negative_epn_overlap ||
        scoreboard.negative_epn_native || scoreboard.negative_epn_nak || scoreboard.negative_mixed_peer)
      `uvm_fatal("OCP_FIFO_EPN_GUARD", "FIFO EPN does not own FS/reset/L2/STALL/replacement or foreign checker controls")
    foreach (ocp_cfg.epn_profiles[i])
      if (ocp_cfg.epn_profiles[i] != null || scoreboard.model.epn_models[i] != null)
        `uvm_fatal("OCP_FIFO_EPN_GUARD", "FIFO EPN requires one fresh selected peer profile")
    void'($value$plusargs("usb_ocp_fifo_epn_peer=%s",peer));
    if (!(peer inside {"DEV0","DEV1"}))
      `uvm_fatal("OCP_FIFO_EPN_GUARD", "Unsupported FIFO EPN peer")
    epn_device = (peer == "DEV0") ? 1 : 2;
    fifo_checker.epn_device = epn_device;
    fifo_checker.ocp_cfg = ocp_cfg;
    armed = 0;
    full = 0;
    // Diagnose a genuine full-depth hang without forced progress or clearing
    // any accepted byte obligation. The profile superclass retains discovery,
    // ordinary four-actor lifecycle and final exact recovery/drain checks.
    fork
      begin super.body(); end
      begin
        fork
          begin wait (fifo_checker.experiment_armed); armed = 1; end
          begin #(ocp_cfg.actor_timeout); end
        join_any
        disable fork;
        if (!armed)
          `uvm_fatal("OCP_FIFO_EPN_WAIT", "Image experiment never armed; discovery/profile obligations retained")
        fork
          begin wait (fifo_checker.full_status_seen); full = 1; end
          begin #4ms; end
        join_any
        disable fork;
        if (!full)
          `uvm_fatal("OCP_FIFO_EPN_WAIT",$sformatf(
            "Advertised-capacity witness timeout: capacity_words=%0d accepted=%0d returned=%0d prefix=%0b hold=%0b; blocked/EPN/retry/recovery obligations remain",
            fifo_checker.model.fifo_depth_words,fifo_checker.model.accepted_bytes,
            fifo_checker.model.returned_bytes,fifo_checker.full_prefix_seen,
            fifo_checker.dma_hold_entered))
      end
    join
  endtask
endclass
