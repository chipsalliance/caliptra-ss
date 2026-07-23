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

package caliptra_ss_usb_common_pkg;

import svt_uvm_pkg::*;
import svt_usb_uvm_pkg::*;

// Consumers outside caliptra_ss_usb_test_pkg must import this package
// directly; SystemVerilog wildcard imports are not re-exported.

// Confirm that a host-to-device transfer delivered the complete requested DATA
// stage. This does not by itself declare the complete control transfer
// successful; protocol-specific code may use it when DATA-stage side effects
// precede status-stage completion.
function automatic bit caliptra_ss_usb_out_payload_complete(
    input svt_usb_transfer transfer);

    int start_index;
    int end_index;

    if ((transfer == null) ||
        (transfer.setup_data_bmrequesttype_dir !=
            svt_usb_types::HOST_TO_DEVICE) ||
        (transfer.status != svt_sequence_item::ACCEPT) ||
        (transfer.payload == null)) begin
        return 1'b0;
    end

    start_index = transfer.payload_start_ix;
    end_index = transfer.payload_end_ix;
    if ((start_index < 0) || (end_index < start_index) ||
        (end_index > transfer.payload.data.size())) begin
        return 1'b0;
    end
    return (end_index - start_index) >= transfer.setup_data_w_length;
endfunction

// Synopsys USB VIP svt_usb_transfer::results_status bit 5 records that a
// host-side transfer finished due to a zero-length data packet. That is a
// successful USB transfer termination, not an error. All other result bits
// remain error conditions for these USB 2.0 control-transfer tests.
function automatic bit caliptra_ss_usb_xfer_successful(
    input svt_usb_transfer transfer);

    if ((transfer == null) ||
        (transfer.status == svt_sequence_item::ABORTED)) begin
        return 1'b0;
    end

    return (transfer.results_status == '0) ||
           (transfer.results_status == (1 << 5));
endfunction

endpackage
