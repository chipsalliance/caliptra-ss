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

class usb_ocp_ep0_retry_observer extends usb_ocp_observer;
  `uvm_component_utils(usb_ocp_ep0_retry_observer)
  usb_ocp_ep0_retry_control control;

  function new(string name = "usb_ocp_ep0_retry_observer", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual function void ocp_configure_transfer_snapshot(
      svt_usb_transfer xfer, usb_ocp_event item);
    if (control != null && xfer == control.selected_transfer &&
        control.kind == usb_ocp_ep0_retry_control::WRITE_RETRY &&
        control.loss_applied && control.expected_timeout_seen)
      item.expected_device_timeout = 1;
  endfunction
endclass
