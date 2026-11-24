// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

virtual class usb_ocp_protocol_error_seq extends usb_ocp_bringup_seq;
  usb_ocp_scoreboard scoreboard;

  function new(string name = "usb_ocp_protocol_error_seq");
    super.new(name);
  endfunction

  virtual function usb_ocp_base_caliptra_seq ocp_prepare_caliptra();
    usb_ocp_protocol_error_caliptra_seq caliptra;
    caliptra = usb_ocp_protocol_error_caliptra_seq::type_id::create("caliptra");
    caliptra.error_model = scoreboard.model.error_model;
    return caliptra;
  endfunction

  task body();
    if (!uvm_config_db#(usb_ocp_scoreboard)::get(p_sequencer,"","ocp_scoreboard",scoreboard) ||
        scoreboard.model.error_model != null || scoreboard.model.stall_model != null ||
        ocp_cfg.full_speed || scoreboard.reset_model != null || scoreboard.l2_model != null ||
        scoreboard.model.require_dev0_ep0_replacement ||
        scoreboard.model.require_dev1_ep0_overlap ||
        $test$plusargs("usb_ocp_control_zlp_canary"))
      `uvm_fatal("OCP_ERROR_GUARD", "Length/CRC tests require their isolated HS recovery environment")
    foreach (ocp_cfg.epn_profiles[i])
      if (ocp_cfg.epn_profiles[i] != null)
        `uvm_fatal("OCP_ERROR_GUARD", "Length/CRC rows do not own EPN profiles")
    scoreboard.model.error_model =
      usb_ocp_protocol_error_model::type_id::create("protocol_error_model");
    super.body();
  endtask
endclass
