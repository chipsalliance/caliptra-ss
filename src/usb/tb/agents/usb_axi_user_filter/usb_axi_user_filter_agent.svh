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
//
// Agent for one AXI USER filter policy. Requires a usb_axi_user_filter_agent_cfg
// in config_db field "cfg". Always builds the monitor; an active agent also
// builds the driver and sequencer. ap re-exports the monitor's analysis port.
class usb_axi_user_filter_agent #(
  int unsigned UW = 32,
  int unsigned NUM_USERS = 2
) extends uvm_agent;
  `uvm_component_param_utils(usb_axi_user_filter_agent #(UW, NUM_USERS))

  typedef usb_axi_user_filter_item #(UW, NUM_USERS) item_t;
  typedef usb_axi_user_filter_agent_cfg #(UW, NUM_USERS) cfg_t;
  typedef usb_axi_user_filter_driver #(UW, NUM_USERS) driver_t;
  typedef usb_axi_user_filter_monitor #(UW, NUM_USERS) monitor_t;
  typedef usb_axi_user_filter_sequencer #(UW, NUM_USERS) sequencer_t;

  cfg_t cfg;
  driver_t driver;
  monitor_t monitor;
  sequencer_t sequencer;
  uvm_analysis_port #(item_t) ap;

  function new(string name = "usb_axi_user_filter_agent", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(cfg_t)::get(this, "", "cfg", cfg) || cfg == null) begin
      `uvm_fatal("USB_USER_FILTER_AGENT", "Missing usb_axi_user_filter_agent_cfg in config_db field \"cfg\"")
    end
    if (cfg.vif == null) begin
      `uvm_fatal("USB_USER_FILTER_AGENT", "usb_axi_user_filter_agent_cfg has no virtual interface")
    end
    is_active = cfg.is_active;
    monitor = monitor_t::type_id::create("monitor", this);
    if (get_is_active() == UVM_ACTIVE) begin
      driver = driver_t::type_id::create("driver", this);
      sequencer = sequencer_t::type_id::create("sequencer", this);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    monitor.vif = cfg.vif;
    ap = monitor.ap;
    if (get_is_active() == UVM_ACTIVE) begin
      driver.vif = cfg.vif;
      driver.seq_item_port.connect(sequencer.seq_item_export);
    end
  endfunction
endclass
