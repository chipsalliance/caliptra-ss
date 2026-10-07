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

// Specializes the reusable bulk OUT driver for endpoint-skip recovery.
class usb_dev_skip_host_seq extends usb_bulk_out_host_seq;
  `uvm_object_utils(usb_dev_skip_host_seq)

  function new(string name = "usb_dev_skip_host_seq");
    super.new(name);
    transfer_label = "Post-skip recovery bulk OUT";
  endfunction

  virtual function string report_id();
    return "USB_SKIP_HOST";
  endfunction
endclass
