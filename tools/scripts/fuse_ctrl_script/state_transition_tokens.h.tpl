// SPDX-License-Identifier: Apache-2.0
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
#include <stdint.h>

const uint32_t tokens[21][4] = {
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
    {${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_1'][3]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_1'][2]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_1'][1]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_1'][0]}}, // CPTRA_SS_TEST_UNLOCK_TOKEN_1
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
    {${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_2'][3]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_2'][2]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_2'][1]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_2'][0]}}, // CPTRA_SS_TEST_UNLOCK_TOKEN_2
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
    {${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_3'][3]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_3'][2]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_3'][1]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_3'][0]}}, // CPTRA_SS_TEST_UNLOCK_TOKEN_3
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
    {${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_4'][3]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_4'][2]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_4'][1]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_4'][0]}}, // CPTRA_SS_TEST_UNLOCK_TOKEN_4
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
    {${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_5'][3]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_5'][2]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_5'][1]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_5'][0]}}, // CPTRA_SS_TEST_UNLOCK_TOKEN_5
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
    {${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_6'][3]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_6'][2]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_6'][1]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_6'][0]}}, // CPTRA_SS_TEST_UNLOCK_TOKEN_6
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}, // empty
    {${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_7'][3]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_7'][2]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_7'][1]}, ${tokens['CPTRA_SS_TEST_UNLOCK_TOKEN_7'][0]}}, // CPTRA_SS_TEST_UNLOCK_TOKEN_7
    {${tokens['CPTRA_SS_TEST_EXIT_TO_MANUF_TOKEN'][3]}, ${tokens['CPTRA_SS_TEST_EXIT_TO_MANUF_TOKEN'][2]}, ${tokens['CPTRA_SS_TEST_EXIT_TO_MANUF_TOKEN'][1]}, ${tokens['CPTRA_SS_TEST_EXIT_TO_MANUF_TOKEN'][0]}}, // CPTRA_SS_TEST_EXIT_TO_MANUF_TOKEN
    {${tokens['CPTRA_SS_MANUF_TO_PROD_TOKEN'][3]}, ${tokens['CPTRA_SS_MANUF_TO_PROD_TOKEN'][2]}, ${tokens['CPTRA_SS_MANUF_TO_PROD_TOKEN'][1]}, ${tokens['CPTRA_SS_MANUF_TO_PROD_TOKEN'][0]}}, // CPTRA_SS_MANUF_TO_PROD_TOKEN
    {${tokens['CPTRA_SS_PROD_TO_PROD_END_TOKEN'][3]}, ${tokens['CPTRA_SS_PROD_TO_PROD_END_TOKEN'][2]}, ${tokens['CPTRA_SS_PROD_TO_PROD_END_TOKEN'][1]}, ${tokens['CPTRA_SS_PROD_TO_PROD_END_TOKEN'][0]}}, // CPTRA_SS_PROD_TO_PROD_END_TOKEN
    {${tokens['CPTRA_SS_RMA_TOKEN'][3]}, ${tokens['CPTRA_SS_RMA_TOKEN'][2]}, ${tokens['CPTRA_SS_RMA_TOKEN'][1]}, ${tokens['CPTRA_SS_RMA_TOKEN'][0]}}, // CPTRA_SS_RMA_TOKEN
    {0x00000000, 0x00000000, 0x00000000, 0x00000000}  // empty
};
