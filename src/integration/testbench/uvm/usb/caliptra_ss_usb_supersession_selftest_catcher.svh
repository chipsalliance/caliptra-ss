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

`ifndef CALIPTRA_SS_USB_SUPERSESSION_SELFTEST_CATCHER_SVH
`define CALIPTRA_SS_USB_SUPERSESSION_SELFTEST_CATCHER_SVH
class caliptra_ss_usb_supersession_selftest_catcher extends uvm_report_catcher;
    `uvm_object_utils(caliptra_ss_usb_supersession_selftest_catcher)
    uvm_report_object client;
    bit armed;
    int match_count = 0;

    function new(string name = "caliptra_ss_usb_supersession_selftest_catcher");
        super.new(name);
    endfunction

    virtual function action_e catch();
        if (armed && (get_client() == client) &&
            (get_id() == "SUPERSESSION_COMPARE") &&
            (get_severity() === UVM_ERROR) && (match_count < 2)) begin
            match_count++;
            return CAUGHT;
        end
        return THROW;
    endfunction
endclass
`endif
