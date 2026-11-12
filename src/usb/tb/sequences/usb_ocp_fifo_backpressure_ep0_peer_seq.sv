// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_fifo_backpressure_ep0_peer_seq extends usb_ocp_base_ep0_peer_seq;
  `uvm_object_utils(usb_ocp_fifo_backpressure_ep0_peer_seq)
  usb_ocp_fifo_backpressure_ep0_checker fifo_checker;

  function new(string name = "usb_ocp_fifo_backpressure_ep0_peer_seq");
    super.new(name);
  endfunction

  virtual task ocp_wait_peer_completion(svt_usb_transfer tr, int device);
    int unsigned peer_slot;
    if (fifo_checker == null || tr == null || device != 1 ||
        tr.device_address !== fifo_checker.model.address[1])
      `uvm_fatal("OCP_FIFO_EP0_GUARD", "Missing or wrong FIFO EP0 peer proof owner")
    case (tr.setup_data_brequest)
      svt_usb_types::GET_CONFIGURATION: peer_slot = 0;
      svt_usb_types::GET_DESCRIPTOR: peer_slot = 1;
      default: `uvm_fatal("OCP_FIFO_EP0_GUARD", "Unsupported FIFO EP0 peer proof request")
    endcase
    // The inherited standard helper cannot advance to its next SETUP until
    // the checker has joined actual native completion and SRAM/clear proof.
    fifo_checker.ocp_check_proof_barrier(peer_slot);
  endtask
endclass
