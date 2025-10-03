# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
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

# Taken from caliptra_ss_lcc_st_trans.c
array set tokens {
    0,0 0xb532a0ca  0,1 0x74ce9687  0,2 0xa2ecef9a  0,3 0x6141be65
    1,0 0x72f04808  1,1 0x05f493b4  1,2 0x7790628a  1,3 0x318372c8
    2,0 0x17c78a78  2,1 0xc7b443ef  2,2 0xd6931045  2,3 0x55e74f3c
    3,0 0x1644aa12  3,1 0x79925802  3,2 0xdbc26815  3,3 0x8597a5fa
    4,0 0x34d1ea6e  4,1 0x121f023f  4,2 0x6e9dc51c  4,3 0xc7439b6f
    5,0 0x03fd9df1  5,1 0x20978af4  5,2 0x49db216d  5,3 0xb0225ece
    6,0 0xcfc0871c  6,1 0xc400e922  6,2 0x4290a4ad  6,3 0x7f10dc89
    7,0 0x67e87f3e  7,1 0xae6ee167  7,2 0x802efa05  7,3 0xbaaa3138
    8,0 0x2f533ae9  8,1 0x341d2478  8,2 0x5f066362  8,3 0xb5fe1577
    9,0 0xf622abb6  9,1 0x5d8318f4  9,2 0xc721179d  9,3 0x51c001f2
   10,0 0x25b8649d 10,1 0xe7818e5b 10,2 0x826d5ba4 10,3 0xd6b633a0
   11,0 0x72f04808 11,1 0x05f493b4 11,2 0x7790628a 11,3 0x318372c8
   12,0 0x00000000 12,1 0x00000000 12,2 0x00000000 12,3 0x00000000                                              
}

# Taken from lc_ctrl.c
array set trans_matrix {
    0,0 13    0,1 0     0,2 13    0,3 0     0,4 13    0,5 0     0,6 13    0,7 0     0,8 13    0,9 0     0,10 13     0,11 0     0,12 13    0,13 0     0,14 13    0,15 0     0,16 13    0,17 13    0,18 13    0,19 13    0,20 12
    1,0 13    1,1 13    1,2 12    1,3 13    1,4 12    1,5 13    1,6 12    1,7 13    1,8 12    1,9 13    1,10 12     1,11 13    1,12 12    1,13 13    1,14 12    1,15 13    1,16 8     1,17 9     1,18 10    1,19 12    1,20 12
    2,0 13    2,1 13    2,2 13    2,3 1     2,4 13    2,5 2     2,6 13    2,7 3     2,8 13    2,9 4     2,10 13     2,11 5     2,12 13    2,13 6     2,14 13    2,15 7     2,16 8     2,17 9     2,18 10    2,19 13    2,20 12   
    3,0 13    3,1 13    3,2 13    3,3 13    3,4 12    3,5 13    3,6 12    3,7 13    3,8 12    3,9 13    3,10 12     3,11 13    3,12 12    3,13 13    3,14 12    3,15 13    3,16 8     3,17 9     3,18 10    3,19 12    3,20 12
    4,0 13    4,1 13    4,2 13    4,3 13    4,4 13    4,5 2     4,6 13    4,7 3     4,8 13    4,9 4     4,10 13     4,11 5     4,12 13    4,13 6     4,14 13    4,15 7     4,16 8     4,17 9     4,18 10    4,19 13    4,20 12
    5,0 13    5,1 13    5,2 13    5,3 13    5,4 13    5,5 13    5,6 12    5,7 13    5,8 12    5,9 13    5,10 12     5,11 13    5,12 12    5,13 13    5,14 12    5,15 13    5,16 8     5,17 9     5,18 10    5,19 12    5,20 12
    6,0 13    6,1 13    6,2 13    6,3 13    6,4 13    6,5 13    6,6 13    6,7 3     6,8 13    6,9 4     6,10 13     6,11 5     6,12 13    6,13 6     6,14 13    6,15 7     6,16 8     6,17 9     6,18 10    6,19 13    6,20 12
    7,0 13    7,1 13    7,2 13    7,3 13    7,4 13    7,5 13    7,6 13    7,7 13    7,8 12    7,9 13    7,10 12     7,11 13    7,12 12    7,13 13    7,14 12    7,15 13    7,16 8     7,17 9     7,18 10    7,19 12    7,20 12
    8,0 13    8,1 13    8,2 13    8,3 13    8,4 13    8,5 13    8,6 13    8,7 13    8,8 13    8,9 4     8,10 13     8,11 5     8,12 13    8,13 6     8,14 13    8,15 7     8,16 8     8,17 9     8,18 10    8,19 13    8,20 12
    9,0 13    9,1 13    9,2 13    9,3 13    9,4 13    9,5 13    9,6 13    9,7 13    9,8 13    9,9 13    9,10 12     9,11 13    9,12 12    9,13 13    9,14 12    9,15 13    9,16 8     9,17 9     9,18 10    9,19 12    9,20 12
   10,0 13   10,1 13   10,2 13   10,3 13   10,4 13   10,5 13   10,6 13   10,7 13   10,8 13   10,9 13   10,10 13    10,11 5    10,12 13   10,13 6    10,14 13   10,15 7    10,16 8    10,17 9    10,18 10   10,19 13   10,20 12
   11,0 13   11,1 13   11,2 13   11,3 13   11,4 13   11,5 13   11,6 13   11,7 13   11,8 13   11,9 13   11,10 13    11,11 13   11,12 12   11,13 13   11,14 12   11,15 13   11,16 8    11,17 9    11,18 10   11,19 12   11,20 12
   12,0 13   12,1 13   12,2 13   12,3 13   12,4 13   12,5 13   12,6 13   12,7 13   12,8 13   12,9 13   12,10 13    12,11 13   12,12 13   12,13 6    12,14 13   12,15 7    12,16 8    12,17 9    12,18 10   12,19 13   12,20 12
   13,0 13   13,1 13   13,2 13   13,3 13   13,4 13   13,5 13   13,6 13   13,7 13   13,8 13   13,9 13   13,10 13    13,11 13   13,12 13   13,13 13   13,14 12   13,15 13   13,16 8    13,17 9    13,18 10   13,19 12   13,20 12
   14,0 13   14,1 13   14,2 13   14,3 13   14,4 13   14,5 13   14,6 13   14,7 13   14,8 13   14,9 13   14,10 13    14,11 13   14,12 13   14,13 13   14,14 13   14,15 7    14,16 8    14,17 9    14,18 10   14,19 13   14,20 12
   15,0 13   15,1 13   15,2 13   15,3 13   15,4 13   15,5 13   15,6 13   15,7 13   15,8 13   15,9 13   15,10 13    15,11 13   15,12 13   15,13 13   15,14 13   15,15 13   15,16 8    15,17 9    15,18 10   15,19 12   15,20 12
   16,0 13   16,1 13   16,2 13   16,3 13   16,4 13   16,5 13   16,6 13   16,7 13   16,8 13   16,9 13   16,10 13    16,11 13   16,12 13   16,13 13   16,14 13   16,15 13   16,16 13   16,17 9    16,18 10   16,19 11   16,20 12
   17,0 13   17,1 13   17,2 13   17,3 13   17,4 13   17,5 13   17,6 13   17,7 13   17,8 13   17,9 13   17,10 13    17,11 13   17,12 13   17,13 13   17,14 13   17,15 13   17,16 13   17,17 13   17,18 10   17,19 11   17,20 12
   18,0 13   18,1 13   18,2 13   18,3 13   18,4 13   18,5 13   18,6 13   18,7 13   18,8 13   18,9 13   18,10 13    18,11 13   18,12 13   18,13 13   18,14 13   18,15 13   18,16 13   18,17 13   18,18 13   18,19 13   18,20 12
   19,0 13   19,1 13   19,2 13   19,3 13   19,4 13   19,5 13   19,6 13   19,7 13   19,8 13   19,9 13   19,10 13    19,11 13   19,12 13   19,13 13   19,14 13   19,15 13   19,16 13   19,17 13   19,18 13   19,19 13   19,20 12
   20,0 13   20,1 13   20,2 13   20,3 13   20,4 13   20,5 13   20,6 13   20,7 13   20,8 13   20,9 13   20,10 13    20,11 13   20,12 13   20,13 13   20,14 13   20,15 13   20,16 13   20,17 13   20,18 13   20,19 13   20,20 13
}

# Number of LC states.
set num_lc_states 21

# Randomly choose the next LC state among the all valid ones
# based on the current state and repeat this until the SCRAP
# state is reached.
set end 0
while {$end != 1} {
    lcc_initialization
    # Read current state and counter value.
    set lc_state_curr [read_lc_state]
    set lc_cnt_curr   [read_lc_counter]
    set lc_cnt_next   [expr {$lc_cnt_curr + 1}]
    # If we reached the max state counter (24), end test.
    if {$lc_cnt_curr != 24} {
        puts "current_state $lc_state_curr current_cntn $lc_cnt_curr"
  
        # Determine a set of potential next states using the transition matrix.
        set count 0
        set buf {}
        for {set i 1} {[expr {$lc_state_curr + $i}] < $num_lc_states} {incr i} {
            set next        [expr {$lc_state_curr + $i}]
            set candidate   $trans_matrix($lc_state_curr,$next)
            # If candidate != INV (13) then append to next state buffer.
            if {$candidate != 13} {
                set count [expr {$count + 1}]
                lappend buf $next
            }
        }
    
        # If we got at least one state, randomly pick one.
        if {$count != 0} {
            set random_idx [expr {int(rand()*$count)}]
            set lc_state_next [lindex $buf $random_idx]
            set token_type $trans_matrix($lc_state_curr,$lc_state_next)
            # Check if we need an unlock token.
            # If token_type == ZER (12) then do not use a token.
            set use_token [expr {$token_type == 12 ? 0 : 1}]
            # Get unlock token, 0 token of no token is needed.
            set t0   $tokens($token_type,0)
            set t1   $tokens($token_type,1)
            set t2   $tokens($token_type,2)
            set t3   $tokens($token_type,3)
            # Print the token.
            puts "Using table tokens for state $lc_state_next: \
                [format 0x%08X $t0] [format 0x%08X $t1] \
                [format 0x%08X $t2] [format 0x%08X $t3] (cond=$use_token)"
            # Now conduct the state transition.
            transition_state $lc_state_next $t0 $t1 $t2 $t3 $use_token
            while {1} {
                # Wait until we got a different state that the current one that is not
                # POST_TRANSITION (21) or INVALID (23).
                after 1000
                set lc_state_tmp [read_lc_state]
                if {($lc_state_tmp != $lc_state_curr) && ($lc_state_tmp != 21) && ($lc_state_tmp != 23)} {
                    break
                }
            }
            # If lc_state_next != SCRAP (20).
            if {$lc_state_next != 20} {
                # Check if we are in the right state.
                set lc_state_curr [read_lc_state]
                if {$lc_state_curr != $lc_state_next} {
                    puts "ERROR: incorrect state: exp: $lc_state_next, act: $lc_state_curr"
                    exit 1
                }
                # Check if we reached the expected lc counter.
                set lc_cnt_curr   [read_lc_counter]
                if {$lc_cnt_curr != $lc_cnt_next} {
                    puts "ERROR: incorrect counter: exp: $lc_cnt_next, act: $lc_cnt_curr"
                    exit 1
                }
            } else {
                # We reached the final SCRAP state, end test.
                puts "Info: Reached the final SCRAP state."
                set end 1
            }
        } 
    } else {
        # Reached the max state counter (24), end test.
        set end 1
    }
}

puts "Info: Test finished."
shutdown
