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

// Signatures and add_callback registration follow usb_axi_stress_callbacks.
class usb_ocp_base_axi_callback extends aaxi_callbacks;
  `uvm_object_utils(usb_ocp_base_axi_callback)
  usb_ocp_observer observer;
  int unsigned manager;

  function new(string name = "usb_ocp_base_axi_callback");
    super.new(name);
  endfunction

  virtual task master_read_addr_done(aaxi_device_class bfm, ref aaxi_master_tr tn);
    if (observer == null) `uvm_fatal("OCP_CALLBACK", "Missing observer")
    observer.outstanding_axi[manager]++;
  endtask

  virtual task master_write_addr_done(aaxi_device_class bfm, ref aaxi_master_tr tn);
    if (observer == null) `uvm_fatal("OCP_CALLBACK", "Missing observer")
    observer.outstanding_axi[manager]++;
  endtask

  virtual task read_done(aaxi_device_class bfm, ref aaxi_master_tr tn);
    if (observer == null || observer.outstanding_axi[manager] == 0)
      `uvm_fatal("OCP_CALLBACK", "Read completion without accepted AXI address")
    observer.ocp_capture_axi(tn, manager);
    observer.outstanding_axi[manager]--;
  endtask

  virtual task write_done(aaxi_device_class bfm, ref aaxi_master_tr tn);
    if (observer == null || observer.outstanding_axi[manager] == 0)
      `uvm_fatal("OCP_CALLBACK", "Write completion without accepted AXI address")
    observer.ocp_capture_axi(tn, manager);
    observer.outstanding_axi[manager]--;
  endtask
endclass
