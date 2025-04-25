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
# [1023:0] = ABCDEFEB00000...000F888888A
array set TOKEN_data {
    0 0xFFFFF8E2
    1 0xEBEFCDAB
    2 0x00000000
    3 0x00000000
    4 0x00000000
    5 0x00000000
    6 0x00000000
    7 0x00000000
    8 0x8A8888F8
}

# Digest value is 9d2fee5ed6ad3ab7de49acb632afd8f2c9cddd33d5ed2846c34b9649b3a54fa367343f15908277c6c6779c52fe55fd7d96966232cd03999d90b3fae27f04e213
set dlen_words [array size TOKEN_data]
set dlen_bytes [expr {$dlen_words * 4}]

puts "TAP: Read Debug Module Status Register..."
set val [riscv dmi_read $dmstatus_addr]
puts "TAP: dmstatus: $val"
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
puts "TAP: Triggering MANUF DEBUG REQ programming..."
riscv dmi_write $SS_DBG_MANUF_SERVICE_REG_REQ 0x1
set actual [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_REQ]
puts "TAP: SS_DBG_MANUF_SERVICE_REG_REQ: $actual"

puts "TAP: Set BOOTFSM_GO to High..."
riscv dmi_write $DMI_REG_BOOTFSM_GO_ADDR 0x1


puts "TAP: Check mailbox available"
set lock [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_RSP]
#check if in execute tap state
while {($lock & 0x200) != 0x00000000} {
    after 1000    ;# Wait 1000ms between polls to avoid busy looping.
    set lock [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_RSP]
}
puts "TAP: mailbox is available"

puts "TAP: Acquire mailbox lock..."
set lock [riscv dmi_read $mbox_lock_dmi_addr]
#check if in execute tap state
while {($lock & 0x00000001) != 0x00000000} {
    after 100    ;# Wait 1000ms between polls to avoid busy looping.
    set lock [riscv dmi_read $mbox_lock_dmi_addr]
}
puts "TAP: mailbox lock was acquired"

puts "TAP: Sending TOKEN mailbox command"
riscv dmi_write $mbox_cmd_dmi_addr 0x4d445554
puts "TAP: Sending the TOKEN size"
riscv dmi_write $mbox_dlen_dmi_addr $dlen_bytes
puts "TAP: Sending the TOKEN"
for {set i 0} {$i < $dlen_words} {incr i} {
    set value $TOKEN_data($i)
    riscv dmi_write $mbox_din_dmi_addr $value
    puts "  TAP: Wrote the TOKEN $value"
}
puts "TAP: Set execute..."
riscv dmi_write $mbox_execute_dmi_addr 0x1

puts ""


# Polling UDS programming status
puts "TAP: Polling MANUF DBG status: waiting for in-progress flag..."
set status [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_RSP]
puts "TAP: Expected in-progress flag (bit 3) not set initially. Waiting."
while {([expr {$status & 0x4}] == 0)} {    
    after 10    ;# Wait 10ms between polls to avoid busy looping.
    set status [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_RSP]
}

puts "TAP: In-progress flag set. Programming complete."

# Now, continuously poll until the in-progress flag clears.
while {($status & 0x4) != 0} {
    after 100    ;# Wait 100ms between polls to avoid busy looping.
    set status [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_RSP]
}

puts "TAP: MANUF DBG in-progress flag cleared. Evaluating result..."

# After the in-progress flag is cleared, read the response register.
set rsp_val [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_RSP]
# Check for failure (bit 8, mask 0x80) and success (bit 7, mask 0x40).
set failure [expr {($rsp_val & 0x2) != 0}]
set success [expr {($rsp_val & 0x1) != 0}]

if {$failure} {
    puts "TAP: MANUF DBG failed (failure bit set)."
    shutdown error
} elseif {$success} {
    puts "TAP: MANUF DBG succeeded (success bit set)."
} else {
    puts "TAP: MANUF DBG returned an unexpected status: $rsp_val"
    shutdown error
} 

puts "TAP: MANUF DBG completed successfully."
shutdown

