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

array set TOKEN_data {
    0 0x77777777
    1 0x66666666
    2 0x55555555
    3 0x44444444
    4 0x33333333
    5 0x22222222
    6 0x11111111
    7 0x00000000
    8 0x77777777
    9 0x66666666
    10 0x55555555
    11 0x44444444
    12 0x33333333
    13 0x22222222
    14 0x11111111
    15 0x00000000
    16 0x77777777
    17 0x66666666
    18 0x55555555
    19 0x44444444
    20 0x33333333
    21 0x22222222
    22 0x11111111
    23 0x00000000
    24 0x77777777
    25 0x66666666
    26 0x55555555
    27 0x44444444
    28 0x33333333
    29 0x22222222
    30 0x11111111
    31 0x00000000
}
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
riscv dmi_write $SS_DBG_MANUF_SERVICE_REG_REQ 0x4
set actual [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_REQ]
puts "TAP: SS_DBG_MANUF_SERVICE_REG_REQ: $actual"

puts "TAP: Set BOOTFSM_GO to High..."
riscv dmi_write $DMI_REG_BOOTFSM_GO_ADDR 0x1


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
    riscv dmi_write $mbox_din_dmi_addr $data($i)
    puts "  TAP: Wrote the TOKEN[$i] = $data($i)"
}
puts "TAP: Sending complete command to mailbox"
riscv dmi_write $mbox_status_dmi_addr 0x00000001
puts ""


# Polling UDS programming status
puts "TAP: Polling MANUF DBG status: waiting for in-progress flag..."
set status [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_RSP]
puts "TAP: Expected in-progress flag (bit 3) not set initially. Waiting."
while {([expr {$status & 0x4}] == 0)} {    
    after 5000
    set status [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_RSP]
}

puts "TAP: In-progress flag set. Programming complete."

# Now, continuously poll until the in-progress flag clears.
while {($status & 0x4) != 0} {
    after 1000    ;# Wait 1000ms between polls to avoid busy looping.
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

puts "Put JTAG into a infinite loop!!!"
while {([expr {$status & 0x4}] == 0)} {    
    after 5000
    set status [riscv dmi_read $SS_DBG_MANUF_SERVICE_REG_RSP]
}
shutdown

