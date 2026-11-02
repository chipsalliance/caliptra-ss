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
// Observes one AXI USER filter policy at every clk rising edge. The first
// sample and every later change are written to ap as a SAMPLE item whose
// enable/priv_axi_users and observed_* fields hold the sampled policy. An X
// or Z in any policy bit is reported as an error.
class usb_axi_user_filter_monitor #(
  int unsigned UW = 32,
  int unsigned NUM_USERS = 2
) extends uvm_monitor;
  `uvm_component_param_utils(usb_axi_user_filter_monitor #(UW, NUM_USERS))

  typedef usb_axi_user_filter_item #(UW, NUM_USERS) item_t;

  virtual usb_axi_user_filter_if #(.UW(UW), .NUM_USERS(NUM_USERS)) vif;
  uvm_analysis_port #(item_t) ap;

  function new(string name = "usb_axi_user_filter_monitor", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap = new("ap", this);
  endfunction

  task run_phase(uvm_phase phase);
    item_t observed;
    logic last_enable;
    logic [UW-1:0] last_users [NUM_USERS];
    bit have_sample;
    bit changed;

    if (vif == null) begin
      `uvm_fatal("USB_USER_FILTER_MONITOR", "Virtual interface is not set")
    end
    forever begin
      @(vif.mon_cb);
      changed = !have_sample || vif.mon_cb.enable_axi_user_filtering !== last_enable;
      foreach (last_users[index]) begin
        if (vif.mon_cb.priv_axi_users[index] !== last_users[index]) begin
          changed = 1'b1;
        end
      end
      if (!changed) begin
        continue;
      end
      have_sample = 1'b1;
      last_enable = vif.mon_cb.enable_axi_user_filtering;
      foreach (last_users[index]) begin
        last_users[index] = vif.mon_cb.priv_axi_users[index];
      end

      observed = item_t::type_id::create("observed");
      observed.op = USB_AXI_USER_FILTER_SAMPLE;
      observed.enable = last_enable;
      observed.observed_enable = last_enable;
      foreach (last_users[index]) begin
        observed.priv_axi_users[index] = last_users[index];
        observed.observed_priv_axi_users[index] = last_users[index];
      end
      if ($isunknown(last_enable)) begin
        `uvm_error("USB_USER_FILTER_MONITOR", $sformatf("Filter enable is unknown: %b", last_enable))
      end
      foreach (last_users[index]) begin
        if ($isunknown(last_users[index])) begin
          `uvm_error("USB_USER_FILTER_MONITOR", $sformatf("Allowlist entry %0d is unknown: 0x%0h", index, last_users[index]))
        end
      end
      `uvm_info("USB_USER_FILTER_MONITOR", $sformatf("Policy observed: %s", observed.convert2string()), UVM_MEDIUM)
      ap.write(observed);
    end
  endtask
endclass
