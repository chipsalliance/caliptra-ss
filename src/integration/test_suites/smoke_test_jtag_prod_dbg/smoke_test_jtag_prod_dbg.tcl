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
source [file join $script_dir constant_payloads.tcl]

set CPTRA_DBG_MANUF_SERVICE_REQ_REG     0x70
set CPTRA_DBG_MANUF_SERVICE_RSP_REG     0x71
set CPTRA_SECURITY_STATE_REG            0x7D
set CPTRA_DEBUG_INTENT_REG              0x7F
set DMI_REG_BOOTFSM_GO_ADDR             0x61


# Req Payload
array set REQ_PAYLOAD {
    0 0xFFFFFEBE
    1 0x00000002
    2 0x00000005
}
set req_payload_dlen_words [array size REQ_PAYLOAD]
set req_payload_dlen_bytes [expr {$req_payload_dlen_words * 4}]
# This plus 4 is for checksum


puts "TAP: Writing PROD DEBUG UNLOCK REQ"
riscv dmi_write $CPTRA_DBG_MANUF_SERVICE_REQ_REG 0x2
puts "TAP: Set BOOTFSM_GO to High..."
riscv dmi_write $DMI_REG_BOOTFSM_GO_ADDR 0x1

puts "TAP: Waiting for MAILBOX_AVAILABLE..."
set rsp [riscv dmi_read $CPTRA_DBG_MANUF_SERVICE_RSP_REG]
while {($rsp & 0x200) == 0} {
    after 100
    set rsp [riscv dmi_read $CPTRA_DBG_MANUF_SERVICE_RSP_REG]
}
puts "TAP: Waiting for PROD_DBG_INPROGRESS..."
set rsp [riscv dmi_read $CPTRA_DBG_MANUF_SERVICE_RSP_REG]
while {($rsp & 0x20) == 0} {
    after 100
    set rsp [riscv dmi_read $CPTRA_DBG_MANUF_SERVICE_RSP_REG]
}
puts "TAP: Status Reg of Manuf Resp is $rsp"
puts "TAP: Acquiring mailbox lock..."
set lock [riscv dmi_read $mbox_lock_dmi_addr]
while {($lock & 0x1) != 0} {
    after 50
    set lock [riscv dmi_read $mbox_lock_dmi_addr]
}

puts "TAP: Sending AUTH_DEBUG_UNLOCK_REQ"
riscv dmi_write $mbox_cmd_dmi_addr 0x50445552
riscv dmi_write $mbox_dlen_dmi_addr $req_payload_dlen_bytes
puts "TAP: Sending the Payload Req Data"
for {set i 0} {$i < $req_payload_dlen_words} {incr i} {
    set value $REQ_PAYLOAD($i)
    riscv dmi_write $mbox_din_dmi_addr $value
    puts "  TAP: Wrote the Payload $value"
}
puts "TAP: Set execute..."
riscv dmi_write $mbox_execute_dmi_addr 0x1

puts ""

puts "TAP: Waiting for AUTH_DEBUG_UNLOCK_CHALLENGE response..."
puts "          Poll mailbox status..."
set status [riscv dmi_read $mbox_status_dmi_addr]
#check if in execute tap state
while {($status & 0x0000000F) != 0x00000001} {
    after 100    ;# Wait 1000ms between polls to avoid busy looping.
    set status [riscv dmi_read $mbox_status_dmi_addr]
}
puts "TAP: Read mailbox dlen..."
set set_dlen_bytes [riscv dmi_read $mbox_dlen_dmi_addr]
puts "TAP: Read mailbox data..."
set actual [riscv dmi_read $mbox_dout_dmi_addr]
puts "  TAP: Read the challenge chekcsum $actual"
for {set i 0} {$i < 21} {incr i} {
    set actual [riscv dmi_read $mbox_dout_dmi_addr]
    puts "  TAP: Read the challenge $actual"
}
puts ""
riscv dmi_write $mbox_execute_dmi_addr 0x0
puts "TAP: Acquiring mailbox lock..."
set lock [riscv dmi_read $mbox_lock_dmi_addr]
while {($lock & 0x1) != 0} {
    after 50
    set lock [riscv dmi_read $mbox_lock_dmi_addr]
}
puts "TAP: Write auth resp to mailbox..."
riscv dmi_write $mbox_cmd_dmi_addr 0x50445554
riscv dmi_write $mbox_dlen_dmi_addr $auth_resp_dlen_bytes
# for {set i 0} {$i < $auth_resp_dlen_words} {incr i} {
# checksum+first_data
for {set i 0} {$i < 0x2} {incr i} {
    riscv dmi_write $mbox_din_dmi_addr $Auth_resp_array($i)
}

# !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
# !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
#NOTE: The following code is commented out because it is not used in mimicked ROM.
#NOTE, FIXME: Actual ROM is not available. When ROM is available uncomment the below code
# !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
# !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

# # for {set i 0} {$i < $auth_resp_dlen_words} {incr i} {
# # checksum+first_data
# for {set i 0} {$i < 0x754} {incr i} {
#     riscv dmi_write $mbox_din_dmi_addr $Auth_resp_array($i)
# }


puts "TAP: Set execute..."
riscv dmi_write $mbox_execute_dmi_addr 0x1
puts ""

puts "TAP: AUTH_DEBUG_UNLOCK_TOKEN sent. Waiting for result..."
# Poll for in-progress clear and result
set rsp [riscv dmi_read $CPTRA_DBG_MANUF_SERVICE_RSP_REG]
puts "The first response value is $rsp"
while {($rsp & 0x20) != 0} {
    after 1000
    set rsp [riscv dmi_read $CPTRA_DBG_MANUF_SERVICE_RSP_REG]
}

set success [expr {($rsp & 0x8) != 0}]
set failure [expr {($rsp & 0x10) != 0}]

if {$success} {
    puts "TAP: PROD DEBUG UNLOCK SUCCESS."
} elseif {$failure} {
    puts "TAP: PROD DEBUG UNLOCK FAIL."
    shutdown error
} else {
    puts "TAP: Unexpected unlock result. Status: $rsp"
    shutdown error
}

shutdown

