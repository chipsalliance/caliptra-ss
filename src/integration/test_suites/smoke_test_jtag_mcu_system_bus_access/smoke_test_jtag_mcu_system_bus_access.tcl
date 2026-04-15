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

proc write_read_access {name address access_width patterns} {
    foreach pattern $patterns {
        write_memory $address $access_width $pattern phys
        set actual [read_memory $address $access_width 1 phys ]
        if {[compare $actual $pattern] != 0} {
            puts "mismatch in $name!"
            shutdown error
        }
    }
}

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

#Access MCU SRAM
write_read_access "SRAM" 0x21c00000 8 {0x5a 0xa5}
write_read_access "SRAM" 0x21c00000 16 {0x5a5a 0xa5a5}
write_read_access "SRAM" 0x21c00000 32 {0x5a5a5a5a 0xa5a5a5a5}
write_read_access "SRAM" 0x21c00000 64 {0x5a5a5a5a5a5a5a5a 0xa5a5a5a5a5a5a5a5}

#Access DEBUG_OUT register
write_read_access "DEBUG_OUT" 0x21000414 32 {0x7a7a7a7a 0x85858585}

#Access DEBUG_IN register
write_read_access "DEBUG_IN" 0x21000410 32 {0x7a7a7a7a 0x85858585}

#test boot from MCI SRAM
puts "Write HW override for sram execution"
riscv dmi_write $MCI_DMI_MCI_HW_OVERRIDE 0x1
set actual [riscv dmi_read  $MCI_DMI_MCI_HW_OVERRIDE]
if {[compare $actual 0x1] != 0} {
    puts "mismatch in register MCI_DMI_MCI_HW_OVERRIDE!"
    shutdown error
}
puts "Setting reset vector to MCU SRAM"
riscv dmi_write $MCI_DMI_MCU_RESET_VECTOR 0x21c00010
puts "Setting reset request"
riscv dmi_write $MCI_DMI_RESET_REQUEST 0x1

shutdown
