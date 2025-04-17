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

#––– 1) Register offsets –––
set LC_CTRL_ALERT_TEST_OFFSET                 0x00
set LC_CTRL_STATUS_OFFSET                     0x01
set LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_OFFSET 0x02
set LC_CTRL_CLAIM_TRANSITION_IF_OFFSET        0x03
set LC_CTRL_TRANSITION_REGWEN_OFFSET          0x04
set LC_CTRL_TRANSITION_CMD_OFFSET             0x05
set LC_CTRL_TRANSITION_CTRL_OFFSET            0x06
set LC_CTRL_TRANSITION_TOKEN_0_OFFSET         0x07
set LC_CTRL_TRANSITION_TOKEN_1_OFFSET         0x08
set LC_CTRL_TRANSITION_TOKEN_2_OFFSET         0x09
set LC_CTRL_TRANSITION_TOKEN_3_OFFSET         0x0A
set LC_CTRL_TRANSITION_TARGET_OFFSET          0x0B
set LC_CTRL_OTP_VENDOR_TEST_CTRL_OFFSET       0x0C
set LC_CTRL_OTP_VENDOR_TEST_STATUS_OFFSET     0x0D
set LC_CTRL_LC_STATE_OFFSET                   0x0E
set LC_CTRL_LC_TRANSITION_CNT_OFFSET          0x0F
set LC_CTRL_LC_ID_STATE_OFFSET                0x10
set LC_CTRL_HW_REVISION0_OFFSET               0x11
set LC_CTRL_HW_REVISION1_OFFSET               0x12
set LC_CTRL_DEVICE_ID_0_OFFSET                0x13
set LC_CTRL_DEVICE_ID_1_OFFSET                0x14
set LC_CTRL_DEVICE_ID_2_OFFSET                0x15
set LC_CTRL_DEVICE_ID_3_OFFSET                0x16
set LC_CTRL_DEVICE_ID_4_OFFSET                0x17
set LC_CTRL_DEVICE_ID_5_OFFSET                0x18
set LC_CTRL_DEVICE_ID_6_OFFSET                0x19
set LC_CTRL_DEVICE_ID_7_OFFSET                0x1A
set LC_CTRL_MANUF_STATE_0_OFFSET              0x1B
set LC_CTRL_MANUF_STATE_1_OFFSET              0x1C
set LC_CTRL_MANUF_STATE_2_OFFSET              0x1D
set LC_CTRL_MANUF_STATE_3_OFFSET              0x1E
set LC_CTRL_MANUF_STATE_4_OFFSET              0x1F
set LC_CTRL_MANUF_STATE_5_OFFSET              0x20
set LC_CTRL_MANUF_STATE_6_OFFSET              0x21
set LC_CTRL_MANUF_STATE_7_OFFSET              0x22

#––– 2) Status‑bit masks –––
set CALIPTRA_SS_LC_CTRL_READY_MASK            0x2
set CALIPTRA_SS_LC_CTRL_INIT_MASK             0x1
set CLAIM_TRANS_VAL                            0x96
set TRANSITION_SUCCESSFUL_MASK                0x8
set TRANSITION_COUNT_ERROR_MASK               0x10
set TRANSITION_ERROR_MASK                     0x20
set TOKEN_ERROR_MASK                          0x40
set RMA_ERROR_MASK                            0x80
set OTP_ERROR_MASK                            0x100
set STATE_ERROR_MASK                          0x200
set BUS_INTG_ERROR_MASK                       0x400
set OTP_PARTITION_ERROR_MASK                  0x800

#––– 3) Initialization: poll STATUS until READY, then INIT –––
proc lcc_initialization {} {
    global LC_CTRL_STATUS_OFFSET \
           CALIPTRA_SS_LC_CTRL_READY_MASK \
           CALIPTRA_SS_LC_CTRL_INIT_MASK

    puts "Initializing LC_CTRL…"

    # poll for READY
    set val [riscv dmi_read $LC_CTRL_STATUS_OFFSET]
    while {![expr {($val & $CALIPTRA_SS_LC_CTRL_READY_MASK) >> 1}]} {
        puts "  STATUS=0x[format %X $val], READY bit not set"
        set val [riscv dmi_read $LC_CTRL_STATUS_OFFSET]
    }
    puts "  LC_CTRL is READY"

    # poll for INIT
    set val [riscv dmi_read $LC_CTRL_STATUS_OFFSET]
    while {![expr {($val & $CALIPTRA_SS_LC_CTRL_INIT_MASK)}]} {
        puts "  STATUS=0x[format %X $val], INIT bit not set"
        set val [riscv dmi_read $LC_CTRL_STATUS_OFFSET]
    }
    puts "  LC_CTRL is INITIALIZED"
}

#––– 4) Software transition request –––
proc sw_transition_req {next_lc_state token_31_0 token_63_32 token_95_64 token_127_96 conditional} {
    global LC_CTRL_STATUS_OFFSET \
           LC_CTRL_CLAIM_TRANSITION_IF_OFFSET \
           LC_CTRL_TRANSITION_TARGET_OFFSET \
           LC_CTRL_TRANSITION_TOKEN_0_OFFSET \
           LC_CTRL_TRANSITION_TOKEN_1_OFFSET \
           LC_CTRL_TRANSITION_TOKEN_2_OFFSET \
           LC_CTRL_TRANSITION_TOKEN_3_OFFSET \
           LC_CTRL_TRANSITION_CMD_OFFSET \
           CALIPTRA_SS_LC_CTRL_INIT_MASK \
           CLAIM_TRANS_VAL \
           TRANSITION_SUCCESSFUL_MASK \
           TRANSITION_COUNT_ERROR_MASK \
           TRANSITION_ERROR_MASK \
           TOKEN_ERROR_MASK \
           RMA_ERROR_MASK \
           OTP_ERROR_MASK \
           STATE_ERROR_MASK \
           BUS_INTG_ERROR_MASK \
           OTP_PARTITION_ERROR_MASK

    puts "Starting sw_transition_req → state 0x[format %X $next_lc_state]…"

    # ensure INIT
    set val [riscv dmi_read $LC_CTRL_STATUS_OFFSET]
    while {![expr {($val & $CALIPTRA_SS_LC_CTRL_INIT_MASK)}]} {
        puts "  Waiting INIT, STATUS=0x[format %X $val]"
        set val [riscv dmi_read $LC_CTRL_STATUS_OFFSET]
    }

    # claim mutex
    set loop 0
    while {$loop != $CLAIM_TRANS_VAL} {
        riscv dmi_write $LC_CTRL_CLAIM_TRANSITION_IF_OFFSET $CLAIM_TRANS_VAL
        set loop [expr {[riscv dmi_read $LC_CTRL_CLAIM_TRANSITION_IF_OFFSET] & $CLAIM_TRANS_VAL}]
    }
    puts "  Mutex acquired"

    # set target state
    riscv dmi_write $LC_CTRL_TRANSITION_TARGET_OFFSET $next_lc_state

    # write tokens if conditional
    if {$conditional == 1} {
        riscv dmi_write $LC_CTRL_TRANSITION_TOKEN_0_OFFSET $token_31_0
        riscv dmi_write $LC_CTRL_TRANSITION_TOKEN_1_OFFSET $token_63_32
        riscv dmi_write $LC_CTRL_TRANSITION_TOKEN_2_OFFSET $token_95_64
        riscv dmi_write $LC_CTRL_TRANSITION_TOKEN_3_OFFSET $token_127_96
    }

    # trigger the transition
    riscv dmi_write $LC_CTRL_TRANSITION_CMD_OFFSET 0x1

    # poll for completion or error
    puts "  Polling STATUS for completion…"
    while {1} {
        set status_val [riscv dmi_read $LC_CTRL_STATUS_OFFSET]
        set TRANSITION_SUCCESSFUL [expr {($status_val & $TRANSITION_SUCCESSFUL_MASK) >> 3}]
        set TRANSITION_COUNT_ERROR [expr {($status_val & $TRANSITION_COUNT_ERROR_MASK) >> 4}]
        set TRANSITION_ERROR [expr {($status_val & $TRANSITION_ERROR_MASK) >> 5}]
        set TOKEN_ERROR [expr {($status_val & $TOKEN_ERROR_MASK) >> 6}]
        set RMA_ERROR [expr {($status_val & $RMA_ERROR_MASK) >> 7}]
        set OTP_ERROR [expr {($status_val & $OTP_ERROR_MASK) >> 8}]
        set STATE_ERROR [expr {($status_val & $STATE_ERROR_MASK) >> 9}]
        set BUS_INTG_ERROR [expr {($status_val & $BUS_INTG_ERROR_MASK) >> 10}]
        set OTP_PARTITION_ERROR [expr {($status_val & $OTP_PARTITION_ERROR_MASK) >> 11}]

        if {$TRANSITION_SUCCESSFUL} {
            puts "  Transition successful"
            break
        } elseif {$TRANSITION_ERROR} {
            puts "  Generic transition error"
            break
        } elseif {$TOKEN_ERROR} {
            puts "  Token error"
            break
        } elseif {$OTP_ERROR} {
            puts "  OTP error"
            break
        } elseif {$RMA_ERROR} {
            puts "  RMA error"
            break
        } elseif {$STATE_ERROR} {
            puts "  State error"
            break
        } elseif {$BUS_INTG_ERROR} {
            puts "  Bus integrity error"
            break
        } elseif {$OTP_PARTITION_ERROR} {
            puts "  OTP partition error"
            break
        }
    }

    # release mutex
    riscv dmi_write $LC_CTRL_CLAIM_TRANSITION_IF_OFFSET 0x0
    puts "sw_transition_req done."
}

#––– 5) Helpers for encoding next state and triggering –––
proc calc_lc_state_mnemonic {state} {
    set s [expr {$state & 0x1F}]
    return [expr {($s<<25)|($s<<20)|($s<<15)|($s<<10)|($s<<5)|$s}]
}

proc transition_state {next_lc_state token_31_0 token_63_32 token_95_64 token_127_96 conditional} {
    set next_lc_state_mne [calc_lc_state_mnemonic $next_lc_state]
    sw_transition_req $next_lc_state_mne $token_31_0 $token_63_32 $token_95_64 $token_127_96 $conditional
    # reset_fc_lcc_rtl
    # puts "LC_CTRL now in state 0x[format %X $next_lc_state_mne]"
}
