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

`ifndef CALIPTRA_SS_USB_OCP_FIFO_FLOW_INDICES_TEST_SV
`define CALIPTRA_SS_USB_OCP_FIFO_FLOW_INDICES_TEST_SV

// OCP_FIFO_011: throttle FIFO writes using the reported read/write indices.
class caliptra_ss_usb_ocp_fifo_flow_indices_test
    extends caliptra_ss_usb_ocp_fifo_flow_control_test;

    `uvm_component_utils(caliptra_ss_usb_ocp_fifo_flow_indices_test)

    function new(
        string name = "caliptra_ss_usb_ocp_fifo_flow_indices_test",
        uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        uvm_config_db#(ocp_fifo_flow_control_strategy_e)::set(
            this, "*", "strategy", FIFO_FLOW_BY_INDICES);
        uvm_config_db#(int unsigned)::set(
            this, "*", "image_dwords", 96);
        uvm_config_db#(time)::set(this, "*", "poll_delay", 100us);
        uvm_config_db#(int unsigned)::set(
            this, "*", "max_polls", 3);
        uvm_config_db#(int unsigned)::set(
            this, "*", "max_retries", 20);
        uvm_config_db#(time)::set(
            this, "*", "completion_wait", 1ms);
        super.build_phase(phase);
    endfunction

endclass

`endif // CALIPTRA_SS_USB_OCP_FIFO_FLOW_INDICES_TEST_SV
