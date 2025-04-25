
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
//


task smoke_test_mcu_trace_buffer_no_debug();
    $display("[%s] Starting smoke test for MCU Trace Buffer No Debug Mode", $time);
    wait_mcu_rst_b_deassert();

    halt_mcu_core(40000);
    
    check_mcu_trace_buffer(1);

    bfm_axi_read_single_check_data_response(`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_STATUS, $urandom(), '0, AXI_RESP_SLVERR);
    bfm_axi_read_single_check_data_response(`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_CONFIG, $urandom(),   '0, AXI_RESP_SLVERR);
    bfm_axi_read_single_check_data_response(`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_DATA, $urandom(),     '0, AXI_RESP_SLVERR);
    bfm_axi_read_single_check_data_response(`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_WRITE_PTR, $urandom(),'0, AXI_RESP_SLVERR);
    bfm_axi_read_single_check_data_response(`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_READ_PTR, $urandom(), '0, AXI_RESP_SLVERR);

    end_test_successful_req();

endtask