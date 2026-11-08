// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_reset_control extends uvm_object;
  `uvm_object_utils(usb_ocp_reset_control)
  typedef enum int {BUS, DEV0, DEV1} scope_e;
  typedef enum int {SETUP, DATA, STATUS, PARTIAL, ACTIVATE} stage_e;
  typedef enum int {NONE, RETENTION, EPOCH, QUIESCENCE, PEER, BYTE_RETENTION} negative_e;
  scope_e scope;
  stage_e stage;
  negative_e negative;
  // Coordination only. The reset model separately requires frontdoor evidence.
  bit armed;
  bit abort_requested;
  bit caliptra_quiescent;
  bit retention_complete;
  bit mcu_reinitialized;
  bit event_complete;
  bit event_dispatched;
  bit fifo_reset_observed;
  bit fresh_zero_observed;
  int unsigned attempt;
  time deadline;

  function new(string name = "usb_ocp_reset_control");
    super.new(name);
  endfunction

  function bit ocp_check_recovery_affected();
    return scope != DEV1;
  endfunction

  function bit ocp_check_device_affected(int device);
    return scope == BUS || (scope == DEV0 && device == 1) ||
                           (scope == DEV1 && device == 2);
  endfunction

  function void ocp_configure_arguments();
    uvm_cmdline_processor cli;
    string values[$];
    string args[$];
    cli = uvm_cmdline_processor::get_inst();
    if (cli.get_arg_values("+usb_ocp_reset_scope=",values) != 1)
      `uvm_fatal("OCP_RESET_GUARD", "Require one +usb_ocp_reset_scope=BUS|DEV0|DEV1")
    case (values[0])
      "BUS": scope = BUS;
      "DEV0": scope = DEV0;
      "DEV1": scope = DEV1;
      default: `uvm_fatal("OCP_RESET_GUARD", "Malformed reset scope")
    endcase
    values.delete();
    if (cli.get_arg_values("+usb_ocp_reset_stage=",values) != 1)
      `uvm_fatal("OCP_RESET_GUARD", "Require one +usb_ocp_reset_stage=SETUP|DATA|STATUS|PARTIAL|ACTIVATE")
    case (values[0])
      "SETUP": stage = SETUP;
      "DATA": stage = DATA;
      "STATUS": stage = STATUS;
      "PARTIAL": stage = PARTIAL;
      "ACTIVATE": stage = ACTIVATE;
      default: `uvm_fatal("OCP_RESET_GUARD", "Malformed reset stage")
    endcase
    values.delete();
    if (cli.get_arg_values("+usb_ocp_reset_negative=",values) > 1)
      `uvm_fatal("OCP_RESET_GUARD", "Duplicate private reset checker control")
    negative = NONE;
    if (values.size() != 0) begin
      case (values[0])
        "RETENTION": negative = RETENTION;
        "EPOCH": negative = EPOCH;
        "QUIESCENCE": negative = QUIESCENCE;
        "PEER": negative = PEER;
        "BYTE_RETENTION": negative = BYTE_RETENTION;
        default: `uvm_fatal("OCP_RESET_GUARD", "Malformed private reset checker control")
      endcase
    end
    if ((negative == PEER && scope == BUS) ||
        (negative inside {RETENTION,QUIESCENCE} && scope == DEV1) ||
        (negative == EPOCH && stage inside {PARTIAL,ACTIVATE}))
      `uvm_fatal("OCP_RESET_GUARD", "Private checker control is incompatible with scope/stage")
    if (negative == BYTE_RETENTION && (scope == DEV1 || stage != PARTIAL))
      `uvm_fatal("OCP_RESET_GUARD", "Byte-retention control requires BUS/DEV0 PARTIAL")
    cli.get_args(args);
    foreach (args[i]) begin
      if (uvm_is_match("+usb_ocp_reset_*",args[i]) &&
          !uvm_is_match("+usb_ocp_reset_scope=*",args[i]) &&
          !uvm_is_match("+usb_ocp_reset_stage=*",args[i]) &&
          !uvm_is_match("+usb_ocp_reset_negative=*",args[i]))
        `uvm_fatal("OCP_RESET_GUARD", "Unknown/missing-value reset control")
      if (uvm_is_match("+usb_ocp_l2*",args[i]) ||
          uvm_is_match("+usb_ocp_epn_type*",args[i]) ||
          uvm_is_match("+usb_ocp_negative*",args[i]) ||
          uvm_is_match("+usb_ocp_control_zlp_canary*",args[i]) ||
          uvm_is_match("+usb_ocp_image_words*",args[i]))
        `uvm_fatal("OCP_RESET_GUARD", "Reset fixture cannot combine with another row's controls or image override")
    end
  endfunction
endclass
