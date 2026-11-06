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

class usb_ocp_base_transfer_callback extends svt_usb_protocol_monitor_callback;
  `uvm_object_utils(usb_ocp_base_transfer_callback)
  usb_ocp_observer observer;

  function new(string name = "usb_ocp_base_transfer_callback");
    super.new(name);
  endfunction

  virtual function void transfer_started(svt_usb_protocol_monitor protocol_mon,
                                         svt_usb_transfer xfer);
    if (observer == null) `uvm_fatal("OCP_CALLBACK", "Missing observer")
    observer.ocp_capture_transfer_start(xfer);
  endfunction

  virtual function void transfer_ended(svt_usb_protocol_monitor protocol_mon,
                                       svt_usb_transfer xfer);
    if (observer == null) `uvm_fatal("OCP_CALLBACK", "Missing observer")
    observer.ocp_capture_transfer(xfer);
  endfunction
endclass
