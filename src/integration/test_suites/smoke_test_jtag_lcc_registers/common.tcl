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
    # write tokens if conditional
    puts "sw_transition_req:: for state $next_lc_state: $token_31_0 $token_63_32 $token_95_64 $token_127_96 (cond=$conditional)"
    if {$conditional == 1} {
        # print them out
        puts "Writing tokens: \
        [format 0x%08X $token_31_0] \
        [format 0x%08X $token_63_32] \
        [format 0x%08X $token_95_64] \
        [format 0x%08X $token_127_96]"
        
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
    puts "transition_state:: for state $next_lc_state: $token_31_0 $token_63_32 $token_95_64 $token_127_96 (cond=$conditional)"
    sw_transition_req $next_lc_state_mne $token_31_0 $token_63_32 $token_95_64 $token_127_96 $conditional
}

#––– 6) Read LC state and counter –––
proc read_lc_state {} {
    global LC_CTRL_LC_STATE_OFFSET
    set raw [riscv dmi_read $LC_CTRL_LC_STATE_OFFSET]
    set state [expr {$raw & 0x1F}]
    puts "LC state register=0x[format %08X $raw], decoded=$state"
    return $state
}

proc read_lc_counter {} {
    global LC_CTRL_LC_TRANSITION_CNT_OFFSET
    set raw [riscv dmi_read $LC_CTRL_LC_TRANSITION_CNT_OFFSET]
    set cnt [expr {$raw & 0x1F}]
    puts "LC counter register=0x[format %08X $raw], count=$cnt"
    return $cnt
}

#––– 7) State sequence and token usage mappings –––
set state_sequence {0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 20}
#––– 7) State sequence and token usage mappings –––
set state_sequence {0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 20}

# define use_token as a proper Tcl list of key/value pairs (no “;”)
array set use_token {
    0 0
    1 1
    2 0
    3 1
    4 0
    5 1
    6 0
    7 1
    8 0
    9 1
    10 0
    11 1
    12 0
    13 1
    14 0
    15 1
    16 1
    17 1
    18 1
    19 0
}



#––– 2) Token true/false –––
set MUBITRUE   0x96
set MUBIFALSE  0x69
#––– 3) Read‑only register tests –––
proc test_read_only_registers {} {
    global \
        LC_CTRL_STATUS_OFFSET \
        LC_CTRL_TRANSITION_REGWEN_OFFSET \
        LC_CTRL_OTP_VENDOR_TEST_STATUS_OFFSET \
        LC_CTRL_LC_STATE_OFFSET \
        LC_CTRL_LC_TRANSITION_CNT_OFFSET \
        LC_CTRL_LC_ID_STATE_OFFSET \
        LC_CTRL_HW_REVISION0_OFFSET \
        LC_CTRL_HW_REVISION1_OFFSET \
        LC_CTRL_DEVICE_ID_0_OFFSET LC_CTRL_DEVICE_ID_1_OFFSET \
        LC_CTRL_DEVICE_ID_2_OFFSET LC_CTRL_DEVICE_ID_3_OFFSET \
        LC_CTRL_DEVICE_ID_4_OFFSET LC_CTRL_DEVICE_ID_5_OFFSET \
        LC_CTRL_DEVICE_ID_6_OFFSET LC_CTRL_DEVICE_ID_7_OFFSET \
        LC_CTRL_MANUF_STATE_0_OFFSET LC_CTRL_MANUF_STATE_1_OFFSET \
        LC_CTRL_MANUF_STATE_2_OFFSET LC_CTRL_MANUF_STATE_3_OFFSET \
        LC_CTRL_MANUF_STATE_4_OFFSET LC_CTRL_MANUF_STATE_5_OFFSET \
        LC_CTRL_MANUF_STATE_6_OFFSET LC_CTRL_MANUF_STATE_7_OFFSET
    puts "============"
    puts "MCU: TESTING RO LCC REGISTERS"
    puts "============\n"

    # STATUS
    set status_exp  [riscv dmi_read $LC_CTRL_STATUS_OFFSET]
    riscv dmi_write $LC_CTRL_STATUS_OFFSET 0xdeadbeef
    set status      [riscv dmi_read $LC_CTRL_STATUS_OFFSET]
    if {$status_exp != $status} {
        puts "ERROR: incorrect value: exp: $status_exp, act: $status"
        exit 1
    }

    # TRANSITION_REGWEN
    set trw_exp     [riscv dmi_read $LC_CTRL_TRANSITION_REGWEN_OFFSET]
    riscv dmi_write $LC_CTRL_TRANSITION_REGWEN_OFFSET 0xdeadbeef
    set trw         [riscv dmi_read $LC_CTRL_TRANSITION_REGWEN_OFFSET]
    if {$trw_exp != $trw} {
        puts "ERROR: incorrect value: exp: $trw_exp, act: $trw"
        exit 1
    }

    # OTP_VENDOR_TEST_STATUS
    set otpsts_exp     [riscv dmi_read $LC_CTRL_OTP_VENDOR_TEST_STATUS_OFFSET]
    riscv dmi_write $LC_CTRL_OTP_VENDOR_TEST_STATUS_OFFSET 0xdeadbeef
    set otpsts         [riscv dmi_read $LC_CTRL_OTP_VENDOR_TEST_STATUS_OFFSET]
    if {$otpsts_exp != $otpsts} {
        puts "ERROR: incorrect value: exp: $otpsts_exp, act: $otpsts"
        exit 1
    }

    # LC_STATE
    set lcst_exp     [riscv dmi_read $LC_CTRL_LC_STATE_OFFSET]
    riscv dmi_write $LC_CTRL_LC_STATE_OFFSET 0xdeadbeef
    set lcst         [riscv dmi_read $LC_CTRL_LC_STATE_OFFSET]
    if {$lcst_exp != $lcst} {
        puts "ERROR: incorrect value: exp: $lcst_exp, act: $lcst"
        exit 1
    }

    # LC_TRANSITION_CNT
    set lcnt_exp     [riscv dmi_read $LC_CTRL_LC_TRANSITION_CNT_OFFSET]
    riscv dmi_write $LC_CTRL_LC_TRANSITION_CNT_OFFSET 0xdeadbeef
    set lcnt         [riscv dmi_read $LC_CTRL_LC_TRANSITION_CNT_OFFSET]
    if {$lcnt_exp != $lcnt} {
        puts "ERROR: incorrect value: exp: $lcnt_exp, act: $lcnt"
        exit 1
    }

    # LC_ID_STATE
    set lidst_exp     [riscv dmi_read $LC_CTRL_LC_ID_STATE_OFFSET]
    riscv dmi_write $LC_CTRL_LC_ID_STATE_OFFSET 0xdeadbeef
    set lidst         [riscv dmi_read $LC_CTRL_LC_ID_STATE_OFFSET]
    if {$lidst_exp != $lidst} {
        puts "ERROR: incorrect value: exp: $lidst_exp, act: $lidst"
        exit 1
    }

    # HW_REVISION0
    set hw0_exp     [riscv dmi_read $LC_CTRL_HW_REVISION0_OFFSET]
    riscv dmi_write $LC_CTRL_HW_REVISION0_OFFSET 0xdeadbeef
    set hw0         [riscv dmi_read $LC_CTRL_HW_REVISION0_OFFSET]
    if {$hw0_exp != $hw0} {
        puts "ERROR: incorrect value: exp: $hw0_exp, act: $hw0"
        exit 1
    }

    # HW_REVISION1
    set hw1_exp     [riscv dmi_read $LC_CTRL_HW_REVISION1_OFFSET]
    riscv dmi_write $LC_CTRL_HW_REVISION1_OFFSET 0xdeadbeef
    set hw1         [riscv dmi_read $LC_CTRL_HW_REVISION1_OFFSET]
    if {$hw1_exp != $hw1} {
        puts "ERROR: incorrect value: exp: $hw1_exp, act: $hw1"
        exit 1
    }

    # DEVICE_ID[0..7]
    foreach idx {0 1 2 3 4 5 6 7} {
        set offset "LC_CTRL_DEVICE_ID_${idx}_OFFSET"
        set dev_exp   [riscv dmi_read [set ${offset}]]
        riscv dmi_write [set ${offset}] 0xdeadbeef
        set dev       [riscv dmi_read [set ${offset}]]
        if {$dev_exp != $dev} {
            puts "ERROR: incorrect device_id${idx}: exp: $dev_exp, act: $dev"
            exit 1
        }
    }

    # MANUF_STATE[0..7]
    foreach idx {0 1 2 3 4 5 6 7} {
        set offset "LC_CTRL_MANUF_STATE_${idx}_OFFSET"
        set ms_exp    [riscv dmi_read [set ${offset}]]
        riscv dmi_write [set ${offset}] 0xdeadbeef
        set ms        [riscv dmi_read [set ${offset}]]
        if {$ms_exp != $ms} {
            puts "ERROR: incorrect manuf_state${idx}: $ms_exp, act: $ms"
            exit 1
        }
    }

    puts "============"
    puts "MCU: TESTING RO LCC REGISTERS FINISHED"
    puts "============\n"
}

#––– 4) Write‑only register tests –––
proc test_write_only_registers {} {
    global LC_CTRL_ALERT_TEST_OFFSET
    puts "============"
    puts "MCU: TESTING WO LCC REGISTERS"
    puts "============\n"

    set reg_value   [riscv dmi_read $LC_CTRL_ALERT_TEST_OFFSET]
    set reg_write_value 0x7

    riscv dmi_write $LC_CTRL_ALERT_TEST_OFFSET $reg_write_value

    set reg_value   [riscv dmi_read $LC_CTRL_ALERT_TEST_OFFSET]

    if {$reg_value == $reg_write_value} {
        puts "ERROR: could read write-only register: $reg_value, act: $reg_write_value"
        exit 1
    }

    puts "============"
    puts "MCU: TESTING WO LCC REGISTERS FINISHED"
    puts "============\n"
}

#––– 5) Transition CMD/CTRL tests –––
proc test_transition_cmd_ctrl_registers {} {
    global LC_CTRL_TRANSITION_CMD_OFFSET LC_CTRL_TRANSITION_CTRL_OFFSET
    puts "============"
    puts "MCU: TESTING TRANSITION LCC REGISTERS"
    puts "============\n"

    set cmd [expr {[riscv dmi_read $LC_CTRL_TRANSITION_CMD_OFFSET] & 0x1}]
    if {$cmd != 0} {
        puts "ERROR: incorrect transition_cmd (before write): exp: 0, act: $cmd"
        exit 1
    }

    riscv dmi_write $LC_CTRL_TRANSITION_CMD_OFFSET 0x0
    set cmd [expr {[riscv dmi_read $LC_CTRL_TRANSITION_CMD_OFFSET] & 0x1}]
    if {$cmd != 0} {
        puts "ERROR: incorrect transition_cmd (after write): exp: 0, act: $cmd"
        exit 1
    }

    set ctrl [expr {[riscv dmi_read $LC_CTRL_TRANSITION_CTRL_OFFSET] & 0x3}]
    if {$ctrl != 0} {
        puts "ERROR: incorrect transition_ctrl: exp: 0, act: $ctrl"
        exit 1
    }

    puts "============"
    puts "MCU: TESTING TRANSITION LCC REGISTERS FINISHED"
    puts "============\n"
}

#––– 6) Helper for token check –––
proc check_transition_tokens {act0 act1 act2 act3 exp0 exp1 exp2 exp3} {
    foreach {a e name} [list $act0 $exp0 0 $act1 $exp1 1 $act2 $exp2 2 $act3 $exp3 3] {
        if {$a != $e} {
            puts "ERROR: incorrect transition_token${name}: exp: $e, act: $a"
            exit 1
        }
    }
}

#––– 7) Read‑write register tests –––
proc test_read_write_registers {regwen} {
    global \
        LC_CTRL_TRANSITION_TOKEN_0_OFFSET LC_CTRL_TRANSITION_TOKEN_1_OFFSET \
        LC_CTRL_TRANSITION_TOKEN_2_OFFSET LC_CTRL_TRANSITION_TOKEN_3_OFFSET \
        LC_CTRL_TRANSITION_TARGET_OFFSET LC_CTRL_OTP_VENDOR_TEST_CTRL_OFFSET
    puts "=========="
    puts "MCU: TESTING RW LCC REGISTERS WITH REGWEN=$regwen"
    puts "==========\n"

    set t0 [riscv dmi_read $LC_CTRL_TRANSITION_TOKEN_0_OFFSET]
    set t1 [riscv dmi_read $LC_CTRL_TRANSITION_TOKEN_1_OFFSET]
    set t2 [riscv dmi_read $LC_CTRL_TRANSITION_TOKEN_2_OFFSET]
    set t3 [riscv dmi_read $LC_CTRL_TRANSITION_TOKEN_3_OFFSET]
    check_transition_tokens $t0 $t1 $t2 $t3 0 0 0 0
    puts "--------------------1------------------------------"

    set w0 0xB16B00B5
    set w1 0xABADBABE
    set w2 0x000FF1CE
    set w3 0xBAADF00D
    riscv dmi_write $LC_CTRL_TRANSITION_TOKEN_0_OFFSET $w0
    riscv dmi_write $LC_CTRL_TRANSITION_TOKEN_1_OFFSET $w1
    riscv dmi_write $LC_CTRL_TRANSITION_TOKEN_2_OFFSET $w2
    riscv dmi_write $LC_CTRL_TRANSITION_TOKEN_3_OFFSET $w3

    set e0 [expr {$regwen ? $w0 : 0}]
    set e1 [expr {$regwen ? $w1 : 0}]
    set e2 [expr {$regwen ? $w2 : 0}]
    set e3 [expr {$regwen ? $w3 : 0}]

    set t0 [riscv dmi_read $LC_CTRL_TRANSITION_TOKEN_0_OFFSET]
    set t1 [riscv dmi_read $LC_CTRL_TRANSITION_TOKEN_1_OFFSET]
    set t2 [riscv dmi_read $LC_CTRL_TRANSITION_TOKEN_2_OFFSET]
    set t3 [riscv dmi_read $LC_CTRL_TRANSITION_TOKEN_3_OFFSET]
    check_transition_tokens $t0 $t1 $t2 $t3 $e0 $e1 $e2 $e3
    puts "--------------------2------------------------------"

    set tgt_w [expr {0xE011CFD0 & 0x3FFFFFFF}]
    riscv dmi_write $LC_CTRL_TRANSITION_TARGET_OFFSET $tgt_w
    set tgt_e [expr {$regwen ? $tgt_w : 0}]
    set tgt_r [expr {[riscv dmi_read $LC_CTRL_TRANSITION_TARGET_OFFSET] & 0x3FFFFFFF}]
    if {$tgt_r != $tgt_e} {
        puts "ERROR: incorrect transition_target: exp: $tgt_e, act: $tgt_r"
        exit 1
    }

    set otp_w 0xCAFEBABE
    riscv dmi_write $LC_CTRL_OTP_VENDOR_TEST_CTRL_OFFSET $otp_w
    set otp_e [expr {$regwen ? $otp_w : 0}]
    set otp_r [riscv dmi_read $LC_CTRL_OTP_VENDOR_TEST_CTRL_OFFSET]
    if {$otp_r != $otp_e} {
        puts "ERROR: incorrect otp_vendor_test_ctrl: exp: $otp_e, act: $otp_r"
        exit 1
    }

    puts "=========="
    puts "MCU: TESTING RW LCC REGISTERS FINISHED"
    puts "==========\n"
}

#––– 8) CLAIM_TRANSITION_IF tests –––
proc test_transition_if {lock_register} {
    global LC_CTRL_CLAIM_TRANSITION_IF_OFFSET LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_OFFSET MUBITRUE MUBIFALSE
    puts "============"
    puts "MCU: TESTING TRANSITION_IF LCC REGISTERS"
    puts "============\n"

    riscv dmi_write $LC_CTRL_CLAIM_TRANSITION_IF_OFFSET $MUBIFALSE
    set exp0 $MUBIFALSE
    set act0 [expr {[riscv dmi_read $LC_CTRL_CLAIM_TRANSITION_IF_OFFSET] & 0xFF}]
    if {$act0 != $exp0} {
        puts "ERROR: incorrect claim_transition_if: exp: $exp0, act: $act0"
        exit 1
    }

    set regw [expr {[riscv dmi_read $LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_OFFSET] & 0x1}]
    if {$regw != 1} {
        puts "ERROR: incorrect claim_transition_if_regwen: exp: 1, act: $regw"
        exit 1
    }

    if {$lock_register} {
        riscv dmi_write $LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_OFFSET 0
        set act_rw0 [expr {[riscv dmi_read $LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_OFFSET] & 0x1}]
        if {$act_rw0 != 0} {
            puts "ERROR: incorrect claim_transition_if_regwen after lock: exp: 0, act: $act_rw0"
            exit 1
        }
    }

    riscv dmi_write $LC_CTRL_CLAIM_TRANSITION_IF_OFFSET $MUBITRUE
    set exp1 [expr {$lock_register ? $MUBIFALSE : $MUBITRUE}]
    set act1 [expr {[riscv dmi_read $LC_CTRL_CLAIM_TRANSITION_IF_OFFSET] & 0xFF}]
    if {$act1 != $exp1} {
        puts "ERROR: incorrect claim_transition_if after write: exp: $exp1, act: $act1"
        exit 1
    }

    puts "============"
    puts "MCU: TESTING TRANSITION_IF LCC REGISTERS FINISHED"
    puts "============\n"
}
