// SPDX-License-Identifier: Apache-2.0
// 
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

#ifndef LC_CTRL_H
#define LC_CTRL_H

#include <stdint.h>
#include <stdbool.h>
#include "caliptra_ss_lib.h"

#define NUM_LC_STATES 21
#define NUM_TOKENS 12

#define CPTRA_SS_LC_CTRL_RAW_UNLOCK_TOKEN \
    0xb532a0ca, 0x74ce9687, 0xa2ecef9a, 0x6141be65

typedef enum {
    RAU, // RAW_UNLOCK
    TU1, // TEST_UNLOCKED1
    TU2, // TEST_UNLOCKED2
    TU3, // TEST_UNLOCKED3
    TU4, // TEST_UNLOCKED4
    TU5, // TEST_UNLOCKED5
    TU6, // TEST_UNLOCKED6
    TU7, // TEST_UNLOCKED7
    TEX, // TEST_EXIT
    DEX, // DEV_EXIT
    PEX, // PROD_EXIT
    RMU, // RAW
    ZER, // ZERO
    INV  // INVALID
} lc_token_type_t;

extern lc_token_type_t trans_matrix[NUM_LC_STATES][NUM_LC_STATES];

extern uint32_t state_sequence[];
extern uint8_t use_token[];
extern uint32_t raw_unlock_token[4];

typedef enum {
    RAW            = 0,
    TEST_UNLOCKED0 = 1,
    TEST_LOCKED0   = 2,
    TEST_UNLOCKED1 = 3,
    TEST_LOCKED1   = 4,
    TEST_UNLOCKED2 = 5,
    TEST_LOCKED2   = 6,
    TEST_UNLOCKED3 = 7,
    TEST_LOCKED3   = 8,
    TEST_UNLOCKED4 = 9,
    TEST_LOCKED4   = 10,
    TEST_UNLOCKED5 = 11,
    TEST_LOCKED5   = 12,
    TEST_UNLOCKED6 = 13,
    TEST_LOCKED6   = 14,
    TEST_UNLOCKED7 = 15,
    MANUF          = 16,
    PROD           = 17,
    PROD_END       = 18,
    RMA            = 19,
    SCRAP          = 20
} lc_state_dec_t;

// Repeatedly read the lc_ctrl status register and wait until the lcc
// reports itself to be ready, then initialized.
void lcc_initialization(void);

// Force signals to override LC tokens to a particular set of known values.
void force_lcc_tokens(void);

// Request an LC state transition to next_lc_state. If token is not
// null, it will be written to the four transition token registers
// beforehand.
//
// This returns true if the transition was successful.
//
//   next_lc_state:    The target LC state, described as the replicated mnemonic value.
//
//   token:            A list of four 32-bit words with a token to perform the transition, or NULL
//                     if there is no token.
bool sw_transition_req(uint32_t next_lc_state, const uint32_t token[4]);

// Analogous to sw_transition_req, but expecting the transition to fail.
bool sw_transition_req_with_expec_error(uint32_t next_lc_state, const uint32_t token[4]);

// Request an LC state transition to next_lc_state. If token is not
// null, it will be written to the four transition token registers
// beforehand.
//
// If the request succeeded, reset fuse_ctrl and lc_ctrl before
// returning (so that lc_ctrl can read in the new LC state).
//
// This returns true if the transition suceeded.
//
//   next_lc_state:    The target LC state, described a 5-bit index that will
//                     be replicated to form a mnemonic.
//
//   token:            A list of four 32-bit words with a token to perform the
//                     transition, or NULL if there is no token.
bool transition_state(uint8_t next_lc_state, const uint32_t token[4]);

// Analogous to transition_state, but expecting the transition to fail.
bool transition_state_req_with_expec_error(uint8_t next_lc_state, const uint32_t token[4]);

// The same as transition_state (not expecting an error), but followed
// by a check that the LC state is as requested.
bool transition_state_check(uint8_t next_lc_state, const uint32_t token[4]);

void force_PPD_pin(void);

// Look at the lc_state register and return the 5-bit index that has
// been replicated to get it. If there is no such index, return 0xff.
uint8_t read_lc_state(void);

// Check that the lc_state register reports the current state to be a
// replication of the given 5-bit index. If there is a mismatch, print
// an error (using desc as a human-readable description of the
// expected state) and return false.
bool check_lc_state(const char *desc, uint8_t exp_idx);

uint32_t read_lc_counter(void);
void disable_lcc_SVAs(void);
void enable_lcc_SVAs(void);

#endif // LC_CTRL_H
