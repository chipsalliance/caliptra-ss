// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_protocol_stall_overlap_seq extends usb_ocp_bringup_seq;
  `uvm_object_utils(usb_ocp_protocol_stall_overlap_seq)
  usb_ocp_scoreboard scoreboard;

  function new(string name = "usb_ocp_protocol_stall_overlap_seq");
    super.new(name);
  endfunction

  virtual function usb_ocp_base_host_seq ocp_prepare_host();
    usb_ocp_protocol_stall_host_seq host;
    host = usb_ocp_protocol_stall_host_seq::type_id::create("host");
    host.scoreboard = scoreboard;
    host.stall_model = scoreboard.model.stall_model;
    return host;
  endfunction

  virtual function usb_ocp_base_mcu_seq ocp_prepare_mcu();
    usb_ocp_protocol_stall_mcu_seq mcu;
    mcu = usb_ocp_protocol_stall_mcu_seq::type_id::create("mcu");
    mcu.stall_model = scoreboard.model.stall_model;
    return mcu;
  endfunction

  task body();
    if (!uvm_config_db#(usb_ocp_scoreboard)::get(p_sequencer,"","ocp_scoreboard",scoreboard) ||
        scoreboard.model.stall_model != null)
      `uvm_fatal("OCP_STALL_GUARD", "Missing mandatory checker or duplicate protocol STALL owner")
    if (ocp_cfg.full_speed || scoreboard.l2_model != null || scoreboard.reset_model != null ||
        scoreboard.model.require_dev0_ep0_replacement ||
        scoreboard.model.require_dev1_ep0_overlap ||
        $test$plusargs("usb_ocp_control_zlp_canary"))
      `uvm_fatal("OCP_STALL_GUARD", "Protocol STALL row does not own FS/reset/L2/replacement/ZLP-canary modes")
    foreach (ocp_cfg.epn_profiles[i])
      if (ocp_cfg.epn_profiles[i] != null)
        `uvm_fatal("OCP_STALL_GUARD", "Protocol STALL row uses independent device1 EP0, not EPN windows")
    scoreboard.model.stall_model =
      usb_ocp_protocol_stall_model::type_id::create("protocol_stall_model");
    if ($test$plusargs("usb_ocp_stall_negative_"))
      `uvm_info("OCP_STALL_NEGATIVE", "Owned checker-only control enabled; this run MUST fail", UVM_NONE)
    super.body();
  endtask
endclass
