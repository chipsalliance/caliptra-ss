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

puts "Read Debug Module Status Register..."
set val [riscv dmi_read $dmstatus_addr]
puts "dmstatus: $val"
if {($val & 0x00000c00) == 0} {
    echo "The hart is halted!"
    shutdown error
}
puts ""

#enabling system bus for mem accesses
riscv set_mem_access sysbus

set golden5a {0x5a5a5a5a}
set goldena5 {0xa5a5a5a5}

#Check MCU SRAM
for {set i 0x0} {$i < 16} {incr i} {
    #Write data that is address inverte
    set wr_addr [expr {1 << $i}]
    puts "Writing SRAM addr $wr_addr"
    set wr_data [expr {$wr_addr ^ 0xffffffff}]
    riscv dmi_write $MCI_DMI_MCU_SRAM_ADDR $wr_addr
    riscv dmi_write $MCI_DMI_MCU_SRAM_DATA $wr_data
}

for {set i 0x0} {$i < 16} {incr i} {
    #Expected data that is address inverted
    set rd_addr [expr {1 << $i}]
    puts "Reading SRAM addr $rd_addr"
    set expected [expr {$rd_addr ^ 0xffffffff}]
    riscv dmi_write $MCI_DMI_MCU_SRAM_ADDR $rd_addr
    set actual [riscv dmi_read $MCI_DMI_MCU_SRAM_DATA]
    if {[compare $actual $expected] != 0} {
        puts "mismatch in SRAM address $rd_addr!"
        shutdown error
    }
}

for {set i 0x0} {$i < 17} {incr i} {
    #Write data that is address inverte
    set wr_addr [expr {(1 << $i)-1}]
    puts "Writing SRAM addr $wr_addr"
    set wr_data [expr {$wr_addr ^ 0xffffffff}]
    riscv dmi_write $MCI_DMI_MCU_SRAM_ADDR $wr_addr
    riscv dmi_write $MCI_DMI_MCU_SRAM_DATA $wr_data
}

for {set i 0x0} {$i < 17} {incr i} {
    #Expected data that is address inverted
    set rd_addr [expr {(1 << $i)-1}]
    puts "Reading SRAM addr $rd_addr"
    set expected [expr {$rd_addr ^ 0xffffffff}]
    riscv dmi_write $MCI_DMI_MCU_SRAM_ADDR $rd_addr
    set actual [riscv dmi_read $MCI_DMI_MCU_SRAM_DATA]
    if {[compare $actual $expected] != 0} {
        puts "mismatch in SRAM address $rd_addr!"
        shutdown error
    }
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