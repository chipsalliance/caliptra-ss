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
source [file join $script_dir common.tcl]

array set data {
    0 0x12345678
    1 0xABBACDDC
    2 0xDEADBEEF
    3 0xFEEDBABE
    4 0xBEACCAEB
}
set dlen_words [array size data]
set dlen_bytes [expr {$dlen_words * 4}]

puts "Read Debug Module Status Register..."
set val [riscv dmi_read $dmstatus_addr]
puts "dmstatus: $val"
if {($val & 0x00000c00) == 0} {
    echo "The hart is halted!"
    # shutdown error
}
puts ""


# Define register addresses
set SS_DBG_MANUF_SERVICE_REG_REQ        0x70
set SS_DBG_MANUF_SERVICE_REG_RSP        0x71
set DMI_REG_BOOTFSM_GO_ADDR             0x61

# Write to the debug service register to trigger UDS programming.
puts "Triggering UDS programming..."
riscv dmi_write $SS_DBG_MANUF_SERVICE_REG_REQ 0x4
set actual [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_REQ]
puts "SS_DBG_MANUF_SERVICE_REG_REQ: $actual"

puts "Set BOOTFSM_GO to High..."
riscv dmi_write $DMI_REG_BOOTFSM_GO_ADDR 0x1

# Polling UDS programming status
puts "Polling UDS programming status: waiting for in-progress flag..."
set status [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_RSP]
puts "Expected in-progress flag (bit 9) not set initially. Waiting."
while {([expr {$status & 0x100}] == 0)} {    
    after 5000
    set status [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_RSP]
}

puts "In-progress flag set. Programming complete."

# Now, continuously poll until the in-progress flag clears.
while {($status & 0x100) != 0} {
    after 100    ;# Wait 1000ms between polls to avoid busy looping.
    set status [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_RSP]
}

puts "UDS programming in-progress flag cleared. Evaluating result..."

# After the in-progress flag is cleared, read the response register.
set rsp_val [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_RSP]
# Check for failure (bit 8, mask 0x80) and success (bit 7, mask 0x40).
set failure [expr {($rsp_val & 0x80) != 0}]
set success [expr {($rsp_val & 0x40) != 0}]

if {$failure} {
    puts "UDS programming failed (failure bit set)."
    shutdown error
} elseif {$success} {
    puts "UDS programming succeeded (success bit set)."
} else {
    puts "UDS programming returned an unexpected status: $rsp_val"
    shutdown error
}

puts "UDS programming completed successfully."

shutdown

