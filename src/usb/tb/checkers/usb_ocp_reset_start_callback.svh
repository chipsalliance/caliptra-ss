// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_reset_start_callback extends svt_usb_protocol_callback;
  `uvm_object_utils(usb_ocp_reset_start_callback)
  svt_usb_transfer original;
  bit started;
  bit status_timeout_requested;
  int unsigned status_timeout_responses;
  int status_timeout_index;

  function new(string name = "usb_ocp_reset_start_callback");
    super.new(name);
    status_timeout_requested = 0;
    status_timeout_responses = 0;
    status_timeout_index = -1;
  endfunction

  virtual function void transfer_started(svt_usb_protocol component,
      svt_usb_transfer transfer);
    if (original == null || transfer != original) return;
    if (started)
      `uvm_fatal("OCP_RESET_START", "Duplicate native start for the original control")
    started = 1;
    `uvm_info("OCP_RESET_START", $sformatf(
      "original sequence=%0d transaction=%0d address=%0d native started callback",
      transfer.get_sequence_id(),transfer.get_transaction_id(),
      transfer.device_address), UVM_LOW)
  endfunction

  virtual function void randomized_transaction(svt_usb_protocol component,
      svt_usb_transfer transfer, int transaction_ix,
      svt_usb_types::protocol_randomization_point_enum rand_point);
    svt_usb_transaction transaction;
    svt_usb_types::transaction_type_enum native_type;
    if (!status_timeout_requested || original == null || transfer != original ||
        rand_point != svt_usb_types::PROTOCOL_GEN_20_TRANSACTION_HOST_RESPONSE) return;
    if (!started || transaction_ix < 0 ||
        transaction_ix >= transfer.implementation.size())
      `uvm_fatal("OCP_RESET_STATUS_RESPONSE", "Original response lacks a started, indexed native transaction")
    if (!$cast(transaction,transfer.implementation[transaction_ix]) || transaction == null)
      `uvm_fatal("OCP_RESET_STATUS_RESPONSE", "Original response implementation is not a USB transaction")
    native_type = transaction.get_xact_type_val();
    if (native_type != svt_usb_types::STATUS_TRANSACTION)
      `uvm_fatal("OCP_RESET_STATUS_RESPONSE", $sformatf(
        "Original HOST response is not a native STATUS transaction: %s", native_type.name()))
    if (transfer.get_xfer_type_val() != svt_usb_transfer::CONTROL_TRANSFER ||
        transfer.setup_data_bmrequesttype_dir !== 1'b0 ||
        transfer.setup_data_w_length == 0)
      `uvm_fatal("OCP_RESET_STATUS_RESPONSE", "Native IN response is not the original CONTROL-write STATUS")
    // USB 2.0 8.5.3.1: without HOST ACK, the function retains STATUS.
    // Configure the actual indexed transaction at the native response point.
    transaction.NORMAL_RESPONSE_wt = 0;
    transaction.TIMEOUT_RESPONSE_wt = 1;
    if (!transaction.randomize(host_response) with {
        host_response == svt_usb_transaction::HOST_TIMEOUT_RESPONSE;
      })
      `uvm_fatal("OCP_RESET_STATUS_RESPONSE", "Native HOST timeout response randomization failed")
    if (transaction.host_response != svt_usb_transaction::HOST_TIMEOUT_RESPONSE)
      `uvm_fatal("OCP_RESET_STATUS_RESPONSE", "Native HOST response did not select timeout")
    status_timeout_index = transaction_ix;
    status_timeout_responses++;
    `uvm_info("OCP_RESET_STATUS_RESPONSE", $sformatf(
      "original_sequence=%0d original_transaction=%0d implementation_index=%0d native_type=%s host_response=%s updates=%0d; no omission or survival credit",
      transfer.get_sequence_id(),transfer.get_transaction_id(),transaction_ix,
      native_type.name(),transaction.host_response.name(),status_timeout_responses), UVM_NONE)
  endfunction

endclass
