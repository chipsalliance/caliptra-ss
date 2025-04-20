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


task get_mcu_sram_base_addr(output logic [AXI_AW-1:0] addr);
    addr = `SOC_MCI_TOP_MCU_SRAM_BASE_ADDR;
endtask

task get_mcu_sram_last_addr(output logic [AXI_AW-1:0] addr);
    addr =  `SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + (MCU_SRAM_SIZE_KB * 1024) - 1;
endtask

task get_mcu_sram_size_byte(output int size);
    size = (MCU_SRAM_SIZE_KB * 1024);
endtask

task get_mcu_sram_size_dword(output int size);
    size = (MCU_SRAM_SIZE_KB * 1024) / 4;
endtask


task get_execution_base_address(output logic [AXI_AW-1:0] addr);
    get_mcu_sram_base_addr(addr);
endtask

task set_random_fw_sram_exec_region_size();
    int max_value;
    logic [31:0] fw_sram_exec_value;

    max_value = (MCU_SRAM_SIZE_KB / 4) - 1;
    fw_sram_exec_value = $urandom_range(max_value);

    $display("[%t] Setting FW_SRAM_EXEC_REGION_SIZE to: 0x%x", $time, fw_sram_exec_value);

    bfm_axi_write_single_mcu_lsu(`SOC_MCI_TOP_MCI_REG_FW_SRAM_EXEC_REGION_SIZE, fw_sram_exec_value);

endtask

  
// Task to get the last address of the EXECUTION region
task get_execution_last_address(output logic [AXI_AW-1:0] addr);
    logic [31:0] reg_value;
    logic [AXI_AW-1:0] last_addr;
    logic [AXI_AW-1:0] base_addr;
    logic [AXI_AW-1:0] mcu_last_addr;
    axi_resp_e   resp;
    logic [31:0] rsp_user;
    logic [31:0] read_user;
    read_user = $urandom();
    m_axi_bfm_if.axi_read_single(`SOC_MCI_TOP_MCI_REG_FW_SRAM_EXEC_REGION_SIZE, read_user, , , reg_value, rsp_user, resp); 
    reg_value = reg_value & `MCI_REG_FW_SRAM_EXEC_REGION_SIZE_SIZE_MASK;
    if(resp != AXI_RESP_OKAY) begin
         $error("Read response ERROR: User: 0x%h Address: 0x%h Data: 0x%h",read_user , `MCI_REG_FW_SRAM_EXEC_REGION_SIZE, reg_value);
    end

    get_execution_base_address(base_addr);
    get_mcu_sram_last_addr(last_addr);
    addr = ((reg_value + 1) * 4096) + base_addr - 1; // Last address is one byte before the base of the PROTECTED region. 
                                                     // + 1 because FW_SRAM_EXEC_REGION_SIZE is base 0 meaning 0x0 allocates 
                                                     // 4KB for execution region
    if(addr > last_addr)
        addr = last_addr;
endtask

task get_execution_last_dword_address(output logic [AXI_AW-1:0] addr);
    get_execution_last_address(addr);
    addr[1:0] = 0;
endtask

task get_execution_rand_addr(output logic [AXI_AW-1:0] addr);
    int exec_size;
    logic [AXI_AW-1:0] base_addr;
    get_execution_size(exec_size);
    get_execution_base_address(base_addr);
    addr = ($urandom_range(exec_size) + base_addr) ;
    addr[1:0] = 2'b0;
endtask 

// Task to get the size of the EXECUTION region
task get_execution_size(output int size);
    logic [AXI_AW-1:0] exec_first_addr;
    logic [AXI_AW-1:0] exec_last_addr;
    logic [AXI_AW-1:0] full_size;
    get_execution_last_address(exec_last_addr);
    get_execution_base_address(exec_first_addr);
    full_size = exec_last_addr - exec_first_addr + 1;
    size = full_size;
endtask


// Task to get the base address of the PROTECTED region
task get_protected_base_address(output logic [AXI_AW-1:0] addr);
    logic [AXI_AW-1:0] exec_last_addr;
    get_execution_last_address(exec_last_addr);
    addr = exec_last_addr + 1;
endtask

task get_protected_last_address(output logic [AXI_AW-1:0] addr);
    get_mcu_sram_last_addr(addr);
endtask

task get_protected_size(int size);
    logic [AXI_AW-1:0] prot_first_addr;
    logic [AXI_AW-1:0] prot_last_addr;
    get_protected_last_address(prot_last_addr);
    get_protected_base_address(prot_first_addr);
    size = prot_last_addr - prot_first_addr + 1;
endtask


task mcu_protected_region_exists(output logic exists);
    logic [AXI_AW-1:0] exec_last_addr;
    logic [AXI_AW-1:0] mcu_last_addr;
    get_execution_last_address(exec_last_addr); 
    get_mcu_sram_last_addr(mcu_last_addr);
    exists = exec_last_addr < mcu_last_addr;
endtask

task get_mcu_trace_buffer_entry(input logic [31:0] index, output logic [31:0] entry, input logic no_debug = 0);
    if (index < 0 || index >= 256) begin
        $fatal("Index out of bounds: %d", index);
    end
    if(no_debug) begin
        bfm_axi_write_single_check_response(`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_READ_PTR, $urandom(), index, AXI_RESP_SLVERR);
        bfm_axi_read_single_check_response(`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_DATA, $urandom(), entry, AXI_RESP_SLVERR);
    end
    else begin
        bfm_axi_write_single(`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_READ_PTR, $urandom(), index);
        bfm_axi_read_single(`SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_DATA, $urandom(), entry);
    end
endtask

task check_mcu_trace_buffer_entry(input logic [31:0] index, input logic no_debug = 0);
    logic [31:0] entry;
    $display("[%t] Checking MCU trace buffer entry at index %d", $time, index);
    get_mcu_trace_buffer_entry(index, entry, no_debug);
    if(no_debug) begin
        if(entry !== '0) begin
            $fatal("Data mismatch at index %d: expected %h, got %h", index, '0, entry);
        end
        else begin
            $display("[%t] Entry %d is correct: %h", $time, index, entry);
        end
    end
    else begin
        if(entry !== mcu_trace_buffer[index]) begin
            $fatal("Data mismatch at index %d: expected %h, got %h", index, mcu_trace_buffer[index], entry);
        end
        else begin
            $display("[%t] Entry %d is correct: %h", $time, index, entry);
        end
    end

endtask

task check_mcu_trace_buffer(input logic no_debug = 0);
    $display("[%t] Checking MCU trace buffer", $time);
    for (int i = 0; i < 256; i++) begin
        check_mcu_trace_buffer_entry(i, no_debug);
    end
endtask

task mcu_trace_buffer_force_num_entires(input int num_entries);
    $display("[%t] Forcing MCU trace buffer to have %d entries", $time, num_entries);
    if(num_entries == 64) begin
        wait(mcu_trace_buffer_wr_ptr === 0  && mcu_trace_buffer_valid === 1);
    end
    else begin
        wait((num_entries * 4) === mcu_trace_buffer_wr_ptr);
    end
    force `CPTRA_SS_TOP_PATH.mcu_trace_rv_i_valid_ip = '0;
    $display("%t] MCU trace buffer forced to have %d entries", $time, num_entries);
endtask

task get_mcu_mbox_lock_address(output logic [AXI_AW-1:0] addr);
    addr = `SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK;
endtask

task get_mcu_mbox_valid_axi_user_address(output logic [AXI_AW-1:0] addr);
    addr = `SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_0;
endtask

task get_mcu_mbox_axi_user_lock_address(output logic [AXI_AW-1:0] addr);
    addr = `SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_0;
endtask

task get_mcu_mbox_sram_base_addr(output logic [AXI_AW-1:0] addr, input int mbox_num = 0);
    if (mbox_num == 0)
        addr = `SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR;
    else if (mbox_num == 1)
        addr = `SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_SRAM_BASE_ADDR;
endtask

task get_mcu_mbox_sram_addr(output logic [AXI_AW-1:0] addr, input int dword, input int mbox_num);
    logic [AXI_AW-1:0] base_addr;
    get_mcu_mbox_sram_base_addr(base_addr, mbox_num);
    addr = base_addr + (dword * 4);
endtask

task get_mcu_mbox_dlen_addr(output logic [AXI_AW-1:0] addr, input int mbox_num);
    if (mbox_num == 0)
        addr = `SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN;
    else if (mbox_num == 1)
        addr = `SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_DLEN;
endtask

task get_mbox_mcu_execute_addr(output logic [AXI_AW-1:0] addr, input int mbox_num);
    if (mbox_num == 0)
        addr = `SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE;
    else if (mbox_num == 1)
        addr = `SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_EXECUTE;
endtask

task get_mcu_mbox_cmd_addr(output logic [AXI_AW-1:0] addr, input int mbox_num);
    if (mbox_num == 0)
        addr = `SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD;
    else if (mbox_num == 1)
        addr = `SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_CMD;
endtask

task get_cptra_boot_go_address(output logic [AXI_AW-1:0] addr);
    addr = `SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO;
endtask

task get_mbox_mcu_cmd_status_addr(output logic [AXI_AW-1:0] addr, input int mbox_num);
    if (mbox_num == 0)
        addr = `SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS;
    else if (mbox_num == 1)
        addr = `SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_CMD_STATUS;
endtask

task mcu_trace_buffer_random_inject_trace_data();
    $display("[%t] Randomly injecting trace data into the trace buffer", $time);
    forever begin
        @(posedge `MCI_PATH.i_mci_mcu_trace_buffer.clk);
        #1;
        force `MCU_PATH.trace_rv_i_insn_ip       = $urandom;
        force `MCU_PATH.trace_rv_i_address_ip    = $urandom;
        force `MCU_PATH.trace_rv_i_exception_ip  = $urandom % 2; // Randomize to 0 or 1
        force `MCU_PATH.trace_rv_i_ecause_ip     = $urandom % 32; // Randomize to 5-bit value
        force `MCU_PATH.trace_rv_i_interrupt_ip  = $urandom % 2; // Randomize to 0 or 1
        force `MCU_PATH.trace_rv_i_tval_ip       = $urandom;
    end
endtask
