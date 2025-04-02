// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
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
#include "caliptra_ss_lib.h"

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

void lcc_initialization(void);
void force_lcc_tokens(void);
void sw_transition_req(uint32_t next_lc_state,
                        uint32_t token_31_0,
                        uint32_t token_63_32,
                        uint32_t token_95_64,
                        uint32_t token_127_96,
                        uint32_t conditional);
                        
uint32_t calc_lc_state_mnemonic(uint32_t state);
void transition_state(uint32_t next_lc_state, uint32_t token_31_0, uint32_t token_63_32, uint32_t token_95_64, uint32_t token_127_96, uint32_t conditional);
void transition_state_req_with_expec_error(uint32_t next_lc_state, uint32_t token_31_0, uint32_t token_63_32, uint32_t token_95_64, uint32_t token_127_96, uint32_t conditional);
void test_all_lc_transitions_no_RMA_no_SCRAP(void);
void sw_transition_req_with_expec_error(uint32_t next_lc_state,
    uint32_t token_31_0,
    uint32_t token_63_32,
    uint32_t token_95_64,
    uint32_t token_127_96,
    uint32_t conditional);
void force_PPD_pin(void);


uint32_t read_lc_state(void);

uint32_t read_lc_counter(void);

#endif // LC_CTRL_H