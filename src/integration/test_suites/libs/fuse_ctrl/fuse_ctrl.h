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

#ifndef FUSE_CTRL_H
#define FUSE_CTRL_H

#include <stdint.h>
#include "caliptra_ss_lib.h"

void grant_mcu_for_fc_writes(void);
void grant_caliptra_core_for_fc_writes(void);
void initialize_otp_controller(void);
void sw_transition_req(uint32_t next_lc_state,
                        uint32_t token_127_96,
                        uint32_t token_95_64,
                        uint32_t token_63_32,
                        uint32_t token_31_0,
                        uint32_t conditional);
                        
void dai_wr(uint32_t addr, uint32_t wdata0, uint32_t wdata1, uint32_t granularity, uint32_t exp_mask);
void dai_rd(uint32_t addr, uint32_t* rdata0, uint32_t* rdata1, uint32_t granularity, uint32_t exp_mask);
void wait_dai_op_idle(uint32_t exp_mask);
void calculate_digest(uint32_t partition_base_address);

#endif // FUSE_CTRL_H