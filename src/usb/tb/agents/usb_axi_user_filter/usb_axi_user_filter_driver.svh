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
// Drives one AXI USER filter policy. SET_* items update only the fields their
// op selects, at a clk rising edge; every item then waits one more edge and
// returns a response carrying the policy sampled there, i.e. what the DUT
// sees. The policy is testbench-owned static configuration, so reset is
// ignored. Callers must change the policy only while no filtered transfer is
// in flight.
class usb_axi_user_filter_driver #(
  int unsigned UW = 32,
  int unsigned NUM_USERS = 2
) extends uvm_driver #(usb_axi_user_filter_item #(UW, NUM_USERS));
  `uvm_component_param_utils(usb_axi_user_filter_driver #(UW, NUM_USERS))

  virtual usb_axi_user_filter_if #(.UW(UW), .NUM_USERS(NUM_USERS)) vif;

  function new(string name = "usb_axi_user_filter_driver", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    if (vif == null) begin
      `uvm_fatal("USB_USER_FILTER_DRIVER", "Virtual interface is not set")
    end
    forever begin
      seq_item_port.get_next_item(req);
      drive_item(req);
      seq_item_port.item_done(rsp);
    end
  endtask

  protected task drive_item(usb_axi_user_filter_item #(UW, NUM_USERS) item);
    if (item.op != USB_AXI_USER_FILTER_SAMPLE) begin
      @(vif.drv_cb);
      if (item.updates_enable()) begin
        vif.drv_cb.enable_axi_user_filtering <= item.enable;
      end
      if (item.updates_users()) begin
        foreach (item.priv_axi_users[index]) begin
          vif.drv_cb.priv_axi_users[index] <= item.priv_axi_users[index];
        end
      end
    end
    @(vif.drv_cb);
    if (!$cast(rsp, item.clone())) begin
      `uvm_fatal("USB_USER_FILTER_DRIVER", "Unable to clone the request for its response")
    end
    rsp.set_id_info(item);
    rsp.observed_enable = vif.drv_cb.enable_axi_user_filtering;
    foreach (rsp.observed_priv_axi_users[index]) begin
      rsp.observed_priv_axi_users[index] = vif.drv_cb.priv_axi_users[index];
    end
    `uvm_info("USB_USER_FILTER_DRIVER", $sformatf("Completed %s", rsp.convert2string()), UVM_HIGH)
  endtask
endclass
