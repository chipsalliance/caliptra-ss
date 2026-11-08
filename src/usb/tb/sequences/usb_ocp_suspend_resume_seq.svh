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

class usb_ocp_suspend_resume_seq extends usb_ocp_bringup_seq;
  `uvm_object_utils(usb_ocp_suspend_resume_seq)
  usb_ocp_scoreboard scoreboard;
  usb_ocp_suspend_model l2;

  function new(string name = "usb_ocp_suspend_resume_seq");
    super.new(name);
  endfunction

  virtual function usb_ocp_base_host_seq ocp_prepare_host();
    usb_ocp_suspend_resume_host_seq host;
    host = usb_ocp_suspend_resume_host_seq::type_id::create("host");
    host.scoreboard = scoreboard;
    host.l2 = l2;
    return host;
  endfunction

  task body();
    if (!uvm_config_db#(usb_ocp_scoreboard)::get(p_sequencer,"","ocp_scoreboard",scoreboard))
      `uvm_fatal("OCP_L2_MODEL", "Missing mandatory passive scoreboard")
    l2 = usb_ocp_suspend_model::type_id::create("l2_model");
    l2.mode = usb_ocp_suspend_model::ocp_prepare_mode();
    l2.negative_retention = $test$plusargs("usb_ocp_l2_negative_retention");
    l2.negative_peer = $test$plusargs("usb_ocp_l2_negative_peer");
    l2.negative_progress = $test$plusargs("usb_ocp_l2_negative_progress");
    if ((l2.negative_peer && l2.mode != usb_ocp_suspend_model::DEV0) ||
        (l2.negative_progress && l2.mode != usb_ocp_suspend_model::DEV1))
      `uvm_fatal("OCP_L2_NEGATIVE", "Peer control requires DEV0; DMA progress control requires DEV1")
    l2.core = scoreboard.model;
    l2.ocp_configure_geometry(p_sequencer.reg_model);
    scoreboard.l2_model = l2;
    `uvm_info("OCP_L2_MODE", $sformatf(
      "Pending-image L2 mode=%s; checker-only controls retention=%0b peer=%0b progress=%0b; native service/timer boundaries experimental",
      l2.mode.name(),l2.negative_retention,l2.negative_peer,l2.negative_progress), UVM_LOW)
    super.body();
  endtask
endclass
