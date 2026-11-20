// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_reset_reinit_seq extends usb_ocp_bringup_seq;
  `uvm_object_utils(usb_ocp_reset_reinit_seq)
  usb_ocp_scoreboard scoreboard;
  usb_ocp_reset_model reset_model;

  function new(string name = "usb_ocp_reset_reinit_seq");
    super.new(name);
  endfunction

  virtual function usb_ocp_base_host_seq ocp_prepare_host();
    usb_ocp_reset_reinit_host_seq host;
    host = usb_ocp_reset_reinit_host_seq::type_id::create("host");
    host.reset_model = reset_model;
    host.scoreboard = scoreboard;
    return host;
  endfunction

  virtual function usb_ocp_base_mcu_seq ocp_prepare_mcu();
    usb_ocp_reset_reinit_mcu_seq mcu;
    mcu = usb_ocp_reset_reinit_mcu_seq::type_id::create("mcu");
    mcu.reset_model = reset_model;
    mcu.scoreboard = scoreboard;
    return mcu;
  endfunction

  virtual function usb_ocp_base_caliptra_seq ocp_prepare_caliptra();
    usb_ocp_reset_reinit_caliptra_seq caliptra;
    caliptra = usb_ocp_reset_reinit_caliptra_seq::type_id::create("caliptra");
    caliptra.reset_model = reset_model;
    caliptra.scoreboard = scoreboard;
    return caliptra;
  endfunction

  task body();
    if (!uvm_config_db#(usb_ocp_scoreboard)::get(p_sequencer,"","ocp_scoreboard",scoreboard))
      `uvm_fatal("OCP_RESET_MODEL", "Missing mandatory existing passive scoreboard")
    reset_model = usb_ocp_reset_model::type_id::create("reset_model");
    if (!uvm_config_db#(usb_ocp_reset_control)::get(p_sequencer,"","ocp_reset_control",
                                                reset_model.cfg))
      `uvm_fatal("OCP_RESET_GUARD", "Reset controls were not validated before actors")
    reset_model.core = scoreboard.model;
    reset_model.cfg.deadline = $time + ocp_cfg.actor_timeout;
    ocp_cfg.control_transfer_timeout = 5ms;
    reset_model.ocp_configure_geometry(p_sequencer.reg_model);
    scoreboard.model.reset_commit_at_status = 1;
    scoreboard.reset_model = reset_model;
    foreach (ocp_cfg.epn_profiles[i])
      if (ocp_cfg.epn_profiles[i] != null)
        `uvm_fatal("OCP_RESET_GUARD", "Reset row cannot own an unrelated EPN service profile")
    // Bound software-owned reset/peer service latency within native reset.
    // This does not change reset/debounce/address-recovery signaling timers.
    if (ocp_cfg.service_poll > 10us)
      `uvm_fatal("OCP_RESET_GUARD", "Reset peer service requires service_poll <= 10us")
    if (ocp_cfg.idle_poll_max > 10us) ocp_cfg.idle_poll_max = 10us;
    `uvm_info("OCP_RESET_VARIANT", $sformatf(
      "scope=%s stage=%s negative=%s; source candidate; scaled native timers unchanged",
      reset_model.cfg.scope.name(),reset_model.cfg.stage.name(),
      reset_model.cfg.negative.name()), UVM_LOW)
    super.body();
  endtask
endclass
