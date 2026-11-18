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

`ifndef CALIPTRA_SS_USB_OCP_MALFORMED_TIMEOUT_CATCHER_SVH
`define CALIPTRA_SS_USB_OCP_MALFORMED_TIMEOUT_CATCHER_SVH

class caliptra_ss_usb_ocp_malformed_timeout_catcher extends uvm_report_catcher;
    bit armed;
    int unsigned expected_timeouts;

    function new(string name = "ocp_malformed_timeout_catcher");
        super.new(name);
    endfunction

    virtual function action_e catch();
        if (armed && (expected_timeouts == 0) &&
            (get_severity() == UVM_ERROR) &&
            (get_id() == {"register_fail:LINK 20 TIMING CHECKS:COMMON:",
                          "tend_to_end_delay_check"})) begin
            expected_timeouts++;
            `uvm_info("OCP_ABORT_EXPECTED_NO_RESPONSE",
                "Observed expected native no-response timeout for malformed OUT DATA.",
                UVM_NONE)
            return CAUGHT;
        end
        return THROW;
    endfunction
endclass

`endif
