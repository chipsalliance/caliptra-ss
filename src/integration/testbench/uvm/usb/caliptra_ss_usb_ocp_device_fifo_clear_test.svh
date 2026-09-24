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

`ifndef CALIPTRA_SS_USB_OCP_DEVICE_FIFO_CLEAR_TEST_SV
`define CALIPTRA_SS_USB_OCP_DEVICE_FIFO_CLEAR_TEST_SV

class caliptra_ss_usb_ocp_device_fifo_clear_test
    extends caliptra_ss_usb_ocp_w1dc_access_semantics_test;

    `uvm_component_utils(caliptra_ss_usb_ocp_device_fifo_clear_test)

    function new(
        string name = "caliptra_ss_usb_ocp_device_fifo_clear_test",
        uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        uvm_config_db#(bit)::set(
            this,
            "*",
            "skip_platform_actions",
            1'b1);
        super.build_phase(phase);
    endfunction

endclass

`endif // CALIPTRA_SS_USB_OCP_DEVICE_FIFO_CLEAR_TEST_SV
