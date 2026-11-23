// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_bringup_seq extends usb_ocp_base_seq;
  `uvm_object_utils(usb_ocp_bringup_seq)

  function new(string name = "usb_ocp_bringup_seq");
    super.new(name);
  endfunction

  virtual function usb_ocp_base_host_seq ocp_prepare_host();
    return usb_ocp_base_host_seq::type_id::create("host");
  endfunction

  virtual function usb_ocp_base_mcu_seq ocp_prepare_mcu();
    return usb_ocp_base_mcu_seq::type_id::create("mcu");
  endfunction

  virtual function usb_ocp_base_caliptra_seq ocp_prepare_caliptra();
    return usb_ocp_base_caliptra_seq::type_id::create("caliptra");
  endfunction

  task body();
    usb_ocp_base_host_seq host;
    usb_ocp_base_mcu_seq mcu;
    usb_ocp_base_soc_seq soc;
    usb_ocp_base_caliptra_seq caliptra;
    usb_ocp_observer observer;
    usb_ocp_scoreboard scoreboard;
    bit epn_configured;
    time deadline;
    if (!uvm_config_db#(usb_ocp_observer)::get(p_sequencer,"","ocp_observer",observer) ||
        !uvm_config_db#(usb_ocp_scoreboard)::get(p_sequencer,"","ocp_scoreboard",scoreboard))
      `uvm_fatal("OCP_BRINGUP", "Missing mandatory passive checker")
    if (ocp_cfg.full_speed != scoreboard.model.full_speed ||
        (!ocp_cfg.full_speed && $test$plusargs("usb_ocp_negative_fs_handshake")))
      `uvm_fatal("OCP_FS_GUARD", "FS configuration/checker controls require the owned FS scenario")
    if (scoreboard.reset_model == null && $test$plusargs("usb_ocp_reset"))
      `uvm_fatal("OCP_RESET_GUARD", "Reset controls require the OCP reset/reinitialization testcase")
    if (scoreboard.model.stall_model == null && $test$plusargs("usb_ocp_stall_negative_"))
      `uvm_fatal("OCP_STALL_GUARD", "Protocol STALL controls require the owned testcase")
    if (scoreboard.l2_model == null &&
        ($test$plusargs("usb_ocp_l2_mode") || $test$plusargs("usb_ocp_l2_negative_retention") ||
         $test$plusargs("usb_ocp_l2_negative_peer") || $test$plusargs("usb_ocp_l2_negative_progress")))
      `uvm_fatal("OCP_L2_NEGATIVE", "L2 mode/checker controls require the OCP suspend/resume testcase")
    if (scoreboard.negative_overlap && !scoreboard.model.require_dev1_ep0_overlap)
      `uvm_fatal("OCP_NEGATIVE_CONTROL", "Overlap injection requires a dev1 EP0 overlap scenario")
    if ((scoreboard.negative_replacement || scoreboard.negative_abort_prefix) &&
        !scoreboard.model.require_dev0_ep0_replacement)
      `uvm_fatal("OCP_NEGATIVE_CONTROL", "Replacement injection requires a dev0 EP0 interleave scenario")
    if (scoreboard.negative_mixed_peer && !scoreboard.model.require_mixed_epn)
      `uvm_fatal("OCP_NEGATIVE_CONTROL", "Mixed peer injection requires the paired mixed scenario")
    epn_configured = 0;
    foreach (ocp_cfg.epn_profiles[i]) begin
      if ((ocp_cfg.epn_profiles[i] == null) != (scoreboard.model.epn_models[i] == null))
        `uvm_fatal("OCP_EPN_PROFILE", "Firmware and passive endpoint selection differ")
      if (ocp_cfg.epn_profiles[i] != null) begin
        if (ocp_cfg.epn_profiles[i].device != i+1 ||
            scoreboard.model.epn_models[i].device != i+1)
          `uvm_fatal("OCP_EPN_PROFILE", "Selected endpoint profile has the wrong owner")
        epn_configured = 1;
      end
    end
    if ((scoreboard.negative_epn_overlap || scoreboard.negative_epn_payload ||
         scoreboard.negative_epn_native || scoreboard.negative_epn_nak) &&
        !epn_configured)
      `uvm_fatal("OCP_NEGATIVE_CONTROL", "EPN injection requires the supported EPN profile before actors")
    host = ocp_prepare_host();
    mcu = ocp_prepare_mcu();
    caliptra = ocp_prepare_caliptra();
    soc = usb_ocp_base_soc_seq::type_id::create("soc");
    host.ocp_cfg = ocp_cfg;
    host.observer = observer;
    deadline = $time + ocp_cfg.actor_timeout;
    fork
      host.start(p_sequencer.host_sequencer);
      mcu.start(p_sequencer);
      caliptra.start(p_sequencer);
      soc.start(p_sequencer);
      begin
        // Flags coordinate lifecycle only. They are never transport, payload,
        // discovery, or activation evidence for the independent scoreboard.
        wait (host.completed && caliptra.completed);
        while (!scoreboard.ocp_check_drained()) begin
          if ($time >= deadline) `uvm_fatal("OCP_DRAIN", "Pre-teardown checker drain timeout")
          #1us;
        end
        scoreboard.ocp_check_complete();
        ocp_cfg.stop_requested = 1;
      end
    join
    while (!scoreboard.ocp_check_drained()) begin
      if ($time >= deadline) `uvm_fatal("OCP_DRAIN", "Final checker drain timeout")
      #1us;
    end
    foreach (ocp_cfg.actor_finished[i])
      if (ocp_cfg.actor_finished[i] !== 1)
        `uvm_fatal("OCP_BRINGUP", $sformatf("Actor %0d unfinished",i))
    if (!host.completed || !mcu.completed || !soc.completed || !caliptra.completed)
      `uvm_fatal("OCP_BRINGUP", "Actor returned without completing work")
    scoreboard.ocp_check_complete();
    completed = 1;
  endtask
endclass
