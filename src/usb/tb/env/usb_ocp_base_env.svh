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

class usb_ocp_base_env extends usb_env;
  `uvm_component_utils(usb_ocp_base_env)
  usb_ocp_observer observer;
  usb_ocp_scoreboard scoreboard;
  usb_ocp_base_packet_callback packet_callback;
  usb_ocp_base_transfer_callback transfer_callback;
  usb_ocp_base_service_callback service_callback;
  usb_ocp_suspend_link_callback l2_link_callback;
  usb_ocp_base_axi_callback axi_callback[4];

  function new(string name = "usb_ocp_base_env", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  function void build_phase(uvm_phase phase);
    bit l2_selected;
    super.build_phase(phase);
    observer = usb_ocp_observer::type_id::create("observer",this);
    scoreboard = usb_ocp_scoreboard::type_id::create("scoreboard",this);
    packet_callback = usb_ocp_base_packet_callback::type_id::create("packet_callback");
    transfer_callback = usb_ocp_base_transfer_callback::type_id::create("transfer_callback");
    service_callback = usb_ocp_base_service_callback::type_id::create("service_callback");
    l2_selected = 0;
    void'(uvm_config_db#(bit)::get(this,"","ocp_l2_selected",l2_selected));
    if (l2_selected)
      l2_link_callback = usb_ocp_suspend_link_callback::type_id::create("l2_link_callback");
    foreach (axi_callback[i])
      axi_callback[i] = usb_ocp_base_axi_callback::type_id::create($sformatf("axi_callback%0d",i));
  endfunction

  function void connect_phase(uvm_phase phase);
    usb_ocp_base_env_cfg ocp_cfg;
    super.connect_phase(phase);
    if (!$cast(ocp_cfg,cfg) ||
        !uvm_config_db#(virtual usb_ocp_recovery_if)::get(this,"","ocp_recovery_vif",
                                                       ocp_cfg.recovery_vif))
      `uvm_fatal("OCP_ENV", "Missing architectural recovery interface")
    scoreboard.observer = observer;
    scoreboard.model.ocp_configure_map(reg_model);
    packet_callback.observer = observer;
    transfer_callback.observer = observer;
    observer.service_callback = service_callback;
    observer.l2_link_callback = l2_link_callback;
    foreach (axi_callback[i]) begin
      axi_callback[i].observer = observer;
      axi_callback[i].manager = i;
    end
    uvm_config_db#(usb_ocp_observer)::set(this,"virtual_sequencer","ocp_observer",observer);
    uvm_config_db#(usb_ocp_scoreboard)::set(this,"virtual_sequencer","ocp_scoreboard",scoreboard);
  endfunction

  function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);
    // OCP actors report native access INFO through this sequencer. Keep every
    // other ID/severity and all Avery monitors, callbacks, and trackers intact.
    if (!$test$plusargs("usb_ocp_verbose_access"))
      virtual_sequencer.set_report_severity_id_action(UVM_INFO,"USB_ACCESS",UVM_NO_ACTION);
    if (host_agent.link_mon == null || host_agent.prot_mon == null)
      `uvm_fatal("OCP_ENV", "USB packet/transfer monitors unavailable")
    // Exactly one canonical packet stream; the transfer stream is solely a
    // cross-check. Do not also connect the monitor analysis ports.
    uvm_callbacks#(svt_usb_link_monitor,svt_usb_link_monitor_callback)::add(
      host_agent.link_mon,packet_callback);
    uvm_callbacks#(svt_usb_protocol_monitor,svt_usb_protocol_monitor_callback)::add(
      host_agent.prot_mon,transfer_callback);
    // This OCP topology has one active native host protocol.
    uvm_callbacks#(svt_usb_protocol,svt_usb_protocol_callback)::add(
      null,service_callback);
    if (l2_link_callback != null) begin
      if (host_agent.link == null)
        `uvm_fatal("OCP_ENV", "Selected L2 native link is unavailable")
      uvm_callbacks#(svt_usb_link)::add(host_agent.link,l2_link_callback);
      `uvm_info("OCP_L2_DISPATCH", $sformatf(
        "Native link callback registered on %s",host_agent.link.get_full_name()), UVM_LOW)
    end
    combo_manager.add_callback(axi_callback[0]);
    dev0_memory_manager.add_callback(axi_callback[1]);
    dev1_csr_manager.add_callback(axi_callback[2]);
    dev1_memory_manager.add_callback(axi_callback[3]);
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    scoreboard.ocp_check_complete();
  endfunction
endclass
