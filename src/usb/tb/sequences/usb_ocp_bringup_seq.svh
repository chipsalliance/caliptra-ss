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

  task body();
    usb_ocp_base_host_seq host;
    usb_ocp_base_mcu_seq mcu;
    usb_ocp_base_soc_seq soc;
    usb_ocp_base_caliptra_seq caliptra;
    usb_ocp_observer observer;
    usb_ocp_scoreboard scoreboard;
    time deadline;
    if (!uvm_config_db#(usb_ocp_observer)::get(p_sequencer,"","ocp_observer",observer) ||
        !uvm_config_db#(usb_ocp_scoreboard)::get(p_sequencer,"","ocp_scoreboard",scoreboard))
      `uvm_fatal("OCP_BRINGUP", "Missing mandatory passive checker")
    if (scoreboard.negative_overlap && !scoreboard.model.require_dev1_ep0_overlap)
      `uvm_fatal("OCP_NEGATIVE_CONTROL", "Overlap injection requires a dev1 EP0 overlap scenario")
    host = ocp_prepare_host();
    mcu = usb_ocp_base_mcu_seq::type_id::create("mcu");
    caliptra = usb_ocp_base_caliptra_seq::type_id::create("caliptra");
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
