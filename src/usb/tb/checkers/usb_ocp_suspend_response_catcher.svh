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

// Installed only on this candidate's two native service sequencers. A late
// routing warning is an API experiment failure, never a suppressed response
// or an exception permitting a DUT-pass/deadlock conclusion.
class usb_ocp_suspend_response_catcher extends uvm_report_catcher;
  `uvm_object_utils(usb_ocp_suspend_response_catcher)

  function new(string name = "usb_ocp_suspend_response_catcher");
    super.new(name);
  endfunction

  virtual function action_e catch();
    if (get_severity() == UVM_WARNING && get_id() == "Sequencer") begin
      set_severity(UVM_FATAL);
      set_action(UVM_DISPLAY | UVM_EXIT);
    end
    // Retain the original ID/message and emit the report.
    return THROW;
  endfunction
endclass
