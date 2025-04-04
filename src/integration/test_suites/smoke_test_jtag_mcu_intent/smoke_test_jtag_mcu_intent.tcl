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

array set rw_regs {
    0 MCI_DMI_MCI_BOOTFSM_GO
}

array set rw_reg_mask {
    0 0x1
}

array set ro_regs {
    0 MCI_DMI_HW_FLOW_STATUS
    1 MCI_DMI_RESET_REASON
    2 MCI_DMI_RESET_STATUS
    3 MCI_DMI_HW_ERROR_FATAL
    4 MCI_DMI_AGG_ERROR_FATAL
    5 MCI_DMI_HW_ERROR_NON_FATAL
    6 MCI_DMI_AGG_ERROR_NON_FATAL
}

array set ro_reg_mask {
    0 0xf
    1 0xffffffff
    2 0xffffffff
    3 0xffffffff
    4 0xffffffff
    5 0xffffffff
    6 0xffffffff
}

array set ro_regs_fw_mod {
    0 MCI_DMI_FW_FLOW_STATUS
    1 MCI_DMI_FW_ERROR_FATAL
    2 MCI_DMI_FW_ERROR_NON_FATAL
    3 MCI_DMI_HW_ERROR_ENC
    4 MCI_DMI_FW_ERROR_ENC
    5 MCI_DMI_FW_EXTENDED_ERROR_INFO_0
    6 MCI_DMI_FW_EXTENDED_ERROR_INFO_1
    7 MCI_DMI_FW_EXTENDED_ERROR_INFO_2
    8 MCI_DMI_FW_EXTENDED_ERROR_INFO_3
    9 MCI_DMI_FW_EXTENDED_ERROR_INFO_4
    10 MCI_DMI_FW_EXTENDED_ERROR_INFO_5
    11 MCI_DMI_FW_EXTENDED_ERROR_INFO_6
    12 MCI_DMI_FW_EXTENDED_ERROR_INFO_7
}

array set ro_reg_fw_mod_mask {
    0 0xffffffff
    1 0xffffffff
    2 0xffffffff
    3 0xffffffff
    4 0xffffffff
    5 0xffffffff
    6 0xffffffff
    7 0xffffffff
    8 0xffffffff
    9 0xffffffff
    10 0xffffffff
    11 0xffffffff
    12 0xffffffff
}

array set no_access_regs {
    0 MCI_DMI_RESET_REQUEST
    1 MCI_DMI_CPTRA_BOOT_GO
    2 MCI_DMI_FW_SRAM_EXEC_REGION_SIZE
    3 MCI_DMI_MCU_RESET_VECTOR
    4 MCI_DMI_SS_DEBUG_INTENT
    5 MCI_DMI_SS_CONFIG_DONE
    6 MCI_DMI_SS_CONFIG_DONE_STICKY
    7 MCI_DMI_MCU_NMI_VECTOR
}

set num_rw_regs [array size rw_regs]
set num_ro_regs [array size ro_regs]
set num_ro_regs_fw_mod [array size ro_regs_fw_mod]
set num_no_access_regs [array size ro_regs_mem]

#enabling system bus for mem accesses
#under debug intent we won't be able to access system bus
riscv set_mem_access sysbus

set golden5a {0x5a5a5a5a}
set goldena5 {0xa5a5a5a5}

#Check read only registers that fw modified
puts "Checking the read only registers..."
for {set i 0} {$i < $num_ro_regs_fw_mod} {incr i} {
    set expected [expr {$golden5a & $ro_reg_fw_mod_mask($i)}]
    set actual [riscv dmi_read [set $ro_regs_fw_mod($i)]]
    if {[compare $actual $expected] != 0} {
        puts "mismatch in register $ro_regs_fw_mod($i)!"
        shutdown error
    }
    #try to flip every bit
    set wr_data [expr {$expected ^ 0xffffffff}]
    riscv dmi_write [set $ro_regs_fw_mod($i)] $wr_data
    set actual [riscv dmi_read [set $ro_regs_fw_mod($i)]]
    if {[compare $actual $expected] != 0} {
        puts "mismatch in register $ro_regs_fw_mod($i)!"
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

#Check registers with no access
puts "Checking the no access registers..."
for {set i 0} {$i < $num_no_access_regs} {incr i} {
    set expected 0
    #try to flip every bit
    set wr_data [expr {$expected ^ 0xffffffff}]
    riscv dmi_write [set $no_access_regs($i)] $wr_data
    set actual [riscv dmi_read [set $no_access_regs($i)]]
    if {[compare $actual $expected] != 0} {
        puts "mismatch in register $no_access_regs($i)!"
        shutdown error
    }
}

#Check MCU SRAM
#No access - shouldn't go through
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
    set expected 0
    riscv dmi_write $MCI_DMI_MCU_SRAM_ADDR $rd_addr
    set actual [riscv dmi_read $MCI_DMI_MCU_SRAM_ADDR]
    if {[compare $actual $expected] != 0} {
        puts "mismatch in SRAM address $rd_addr!"
        shutdown error
    }
    set actual [riscv dmi_read $MCI_DMI_MCU_SRAM_DATA]
    if {[compare $actual $expected] != 0} {
        puts "mismatch in SRAM data $rd_addr!"
        shutdown error
    }
}

#Check trace registers, everything should be zero except rd pointer
puts "Checking trace register reads..."
set actual [riscv dmi_read $MCI_DMI_MCU_TRACE_STATUS]
if {[compare $actual 0] != 0} {
    puts "mismatch in register TRACE STATUS!"
    shutdown error
}
set actual [riscv dmi_read $MCI_DMI_MCU_TRACE_CONFIG]
if {[compare $actual 0] != 0} {
    puts "mismatch in register TRACE CONFIG!"
    shutdown error
}
set actual [riscv dmi_read $MCI_DMI_MCU_TRACE_WR_PTR]
if {[compare $actual 0] != 0} {
    puts "mismatch in register TRACE WR PTR!"
    shutdown error
}
set actual [riscv dmi_read $MCI_DMI_MCU_TRACE_RD_PTR]
if {[compare $actual 0] != 0} {
    puts "mismatch in register TRACE RD PTR!"
    shutdown error
}
set actual [riscv dmi_read $MCI_DMI_MCU_TRACE_DATA]
if {[compare $actual 0] != 0} {
    puts "mismatch in register TRACE DATA!"
    shutdown error
}

# Success
puts "Writing BOOTFSM GO to end the test"
riscv dmi_write  $MCI_DMI_MCI_BOOTFSM_GO 0x1
set actual [riscv dmi_read $MCI_DMI_MCI_BOOTFSM_GO]
if {[compare $actual 1] != 0} {
    puts "mismatch in register MCI_DMI_MCI_BOOTFSM_GO!"
    shutdown error
}

shutdown