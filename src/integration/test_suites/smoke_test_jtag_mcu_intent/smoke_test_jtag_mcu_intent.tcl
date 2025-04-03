# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

init

set script_dir [file dirname [info script]]
source [file join $script_dir .. libs jtag common.tcl]

#dmi_reg_bootfsm_go  only 1 bit
#dmi_reg_ss_debug_intent  only 1 bit
#dmi_reg_ss_dbg_manuf_service_reg_req  special access
#dmi_reg_ss_dbg_manuf_service_reg_rsp  read only

#can't be written by FW to test
# dmi_reg_ss_uds_seed_base_addr_l
# dmi_reg_ss_uds_seed_base_addr_h
# dmi_reg_hw_fatal_error
# dmi_reg_hw_non_fatal_error

array set rw_regs {
    0 MCI_DMI_RESET_REQUEST
    1 MCI_DMI_MCI_BOOTFSM_GO
    2 MCI_DMI_CPTRA_BOOT_GO
    3 MCI_DMI_FW_SRAM_EXEC_REGION_SIZE
    4 MCI_DMI_MCU_RESET_VECTOR
    5 MCI_DMI_SS_DEBUG_INTENT
    6 MCI_DMI_SS_CONFIG_DONE
    7 MCI_DMI_SS_CONFIG_DONE_STICKY
    8 MCI_DMI_MCU_NMI_VECTOR
}
array set rw_reg_mask {
    0 0x1
    1 0x1
    2 0x1
    3 0xffff
    4 0xffffffff
    5 0x1
    6 0x1
    7 0x1
    8 0xffffffff
}

array set ro_regs {
    0 MCI_DMI_HW_FLOW_STATUS
    1 MCI_DMI_RESET_REASON
    2 MCI_DMI_RESET_STATUS
    3 MCI_DMI_FW_FLOW_STATUS
    4 MCI_DMI_HW_ERROR_FATAL
    5 MCI_DMI_AGG_ERROR_FATAL
    6 MCI_DMI_HW_ERROR_NON_FATAL
    7 MCI_DMI_AGG_ERROR_NON_FATAL
    8 MCI_DMI_FW_ERROR_FATAL
    9 MCI_DMI_FW_ERROR_NON_FATAL
    10 MCI_DMI_HW_ERROR_ENC
    11 MCI_DMI_FW_ERROR_ENC
    12 MCI_DMI_FW_EXTENDED_ERROR_INFO_0
    13 MCI_DMI_FW_EXTENDED_ERROR_INFO_1
    14 MCI_DMI_FW_EXTENDED_ERROR_INFO_2
    15 MCI_DMI_FW_EXTENDED_ERROR_INFO_3
    16 MCI_DMI_FW_EXTENDED_ERROR_INFO_4
    17 MCI_DMI_FW_EXTENDED_ERROR_INFO_5
    18 MCI_DMI_FW_EXTENDED_ERROR_INFO_6
    19 MCI_DMI_FW_EXTENDED_ERROR_INFO_7
}

array set ro_reg_mask {
    0 0xf
    1 0x0
    2 0x0
    3 0xffffffff
    4 0x0
    5 0x0
    6 0x0
    7 0x0
    8 0xffffffff
    9 0xffffffff
    10 0xffffffff
    11 0xffffffff
    12 0xffffffff
    13 0xffffffff
    14 0xffffffff
    15 0xffffffff
    16 0xffffffff
    17 0xffffffff
    18 0xffffffff
    19 0xffffffff
}

array set ro_regs_mem {
    0 MCI_MEM_HW_FLOW_STATUS
    1 MCI_MEM_RESET_REASON
    2 MCI_MEM_RESET_STATUS
    3 MCI_MEM_FW_FLOW_STATUS
    4 MCI_MEM_HW_ERROR_FATAL
    5 MCI_MEM_AGG_ERROR_FATAL
    6 MCI_MEM_HW_ERROR_NON_FATAL
    7 MCI_MEM_AGG_ERROR_NON_FATAL
    8 MCI_MEM_FW_ERROR_FATAL
    9 MCI_MEM_FW_ERROR_NON_FATAL
    10 MCI_MEM_HW_ERROR_ENC
    11 MCI_MEM_FW_ERROR_ENC
    12 MCI_MEM_FW_EXTENDED_ERROR_INFO_0
    13 MCI_MEM_FW_EXTENDED_ERROR_INFO_1
    14 MCI_MEM_FW_EXTENDED_ERROR_INFO_2
    15 MCI_MEM_FW_EXTENDED_ERROR_INFO_3
    16 MCI_MEM_FW_EXTENDED_ERROR_INFO_4
    17 MCI_MEM_FW_EXTENDED_ERROR_INFO_5
    18 MCI_MEM_FW_EXTENDED_ERROR_INFO_6
    19 MCI_MEM_FW_EXTENDED_ERROR_INFO_7
}

set num_rw_regs [array size rw_regs]
set num_ro_regs [array size ro_regs]
set num_ro_regs_mem [array size ro_regs_mem]

#enabling system bus for mem accesses
#under debug intent we won't be able to access system bus
riscv set_mem_access sysbus

set golden5a {0x5a5a5a5a}
set goldena5 {0xa5a5a5a5}

puts "Checking the writable registers..."
#skipping reset request - do that in different test
for {set i 1} {$i < $num_rw_regs} {incr i} {
    #write golden5a
    riscv dmi_write [set $rw_regs($i)] $golden5a
    set actual [riscv dmi_read [set $rw_regs($i)]]
    set expected [expr {$golden5a & $rw_reg_mask($i)}]
    if {[compare $actual $expected] != 0} {
        puts "mismatch in register $rw_regs($i)!"
        shutdown error
    }
    #write goldena5
    riscv dmi_write [set $rw_regs($i)] $goldena5
    set actual [riscv dmi_read [set $rw_regs($i)]]
    set expected [expr {$goldena5 & $rw_reg_mask($i)}]
    if {[compare $actual $expected] != 0} {
        puts "mismatch in register $rw_regs($i)!"
        shutdown error
    }
}

#Check read only registers
puts "Checking the read only registers..."
for {set i 0} {$i < $num_ro_regs} {incr i} {
    set expected [riscv dmi_read [set $ro_regs($i)]]
    #try to flip every bit
    set wr_data [expr {$expected ^ 0xffffffff}]
    riscv dmi_write [set $ro_regs($i)] $wr_data
    set actual [riscv dmi_read [set $ro_regs($i)]]
    if {[compare $actual $expected] != 0} {
        puts "mismatch in register $ro_regs($i)!"
        shutdown error
    }
}

#Check MCU SRAM
puts "Checking the SRAM interface writes..."
for {set i 0} {$i < 16} {incr i} {
    #Write data that is address inverted
    puts "Writing SRAM addr $i"
    set wr_addr $i
    set wr_data [expr {$i ^ 0xffffffff}]
    riscv dmi_write $MCI_DMI_MCU_SRAM_ADDR $wr_addr
    riscv dmi_write $MCI_DMI_MCU_SRAM_DATA $wr_data
}

puts "Checking the SRAM interface reads..."
for {set i 0} {$i < 16} {incr i} {
    #Expected data that is address inverted
    puts "Reading SRAM addr $i"
    set rd_addr $i
    set expected [expr {$i ^ 0xffffffff}]
    riscv dmi_write $MCI_DMI_MCU_SRAM_ADDR $rd_addr
    set actual [riscv dmi_read $MCI_DMI_MCU_SRAM_DATA]
    if {[compare $actual $expected] != 0} {
        puts "mismatch in SRAM address $rd_addr!"
        shutdown error
    }
}


# Success
#puts "Setting unique value to get MCU to end test"
riscv dmi_write  $MCI_DMI_MCU_RESET_VECTOR 0xB007FACE

shutdown