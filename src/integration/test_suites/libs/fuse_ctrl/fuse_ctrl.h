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
void revoke_grant_mcu_for_fc_writes(void);
void grant_caliptra_core_for_fc_writes(void);
void initialize_otp_controller(void);
void sw_transition_req(uint32_t next_lc_state,
                        uint32_t token_127_96,
                        uint32_t token_95_64,
                        uint32_t token_63_32,
                        uint32_t token_31_0,
                        uint32_t conditional);
void disable_fc_all_ones_sva(void);
void enable_fc_all_ones_sva(void);

// Write wdata0/wdata1 to addr, using granularity to control whether to bother setting the upper
// word. The DAI write command is expected to respond with STATUS equal to exp_status.
//
// On completion, return whether the status was as expected.
bool dai_wr(uint32_t addr, uint32_t wdata0, uint32_t wdata1,
            uint32_t granularity, uint32_t exp_status);

// A version of dai_wr that writes an entire array of fuses with a particular value
//
// This is a bit more efficient than calling dai_wr in a loop, because it doesn't have to set
// wdata0/wdata1 each time.
//
//   first_fuse   The address of the first fuse in the array
//
//   last_fuse   The address of the last fuse in the array
//
//   wdata        A pointer to a pair of uint32_t objects, giving the value to write
//
//   granularity  The number of bits in a fuse.
bool dai_wr_array(uint32_t        first_fuse,
                  uint32_t        last_fuse,
                  const uint32_t *wdata,
                  unsigned        granularity);

// Read from addr, storing the response in *rdata0/*rdata1, where the upper word is only copied back
// if granularity > 32. The DAI read command is expected to respond with STATUS equal to exp_status.
//
// On completion, return whether the status was as expected.
bool dai_rd(uint32_t addr, uint32_t* rdata0, uint32_t* rdata1,
            uint32_t granularity, uint32_t exp_status);

// Wait until the DAI becomes idle (or there is no longer a check pending) or until an error is
// reported. On completion, return whether the status matched exp_status (described below).
//
//   exp_status   If this is zero, the DAI is expected to become idle. If it is nonzero, it contains
//                the error bits that are expected to be set in the first error status that is seen
//                (which will cause the wait to stop). Note that the only bits of this mask that are
//                checked are genuine error bits, so a caller can check that all errors are set by
//                passing UINT32_MAX.
bool wait_dai_op_idle(uint32_t exp_mask);

// Trigger a digest calculation command for the partition with the given base address. Return
// whether the eventual DAI status matched exp_status.
bool calculate_digest(uint32_t partition_base_address, uint32_t exp_status);

// Zeroize the fuse at the given addr, checking the eventual DAI status matched exp_status.
//
// If the eventual DAI status doesn't report an error, check that the rdata registers claim that the
// whole fuse was zeroized. As a special case, the disable_rdata_check argument can be true. If so,
// the check is skipped (used by a test if it wants to inject a reset half-way through the
// zeroization).
//
// Return true if all these checks passed.
bool dai_zer(uint32_t addr, uint32_t granularity, uint32_t exp_status, bool disable_rdata_check);

bool shuffled_dai_wr(uint32_t addr, uint32_t wdata0, uint32_t wdata1,
                     uint32_t granularity, uint32_t exp_status, uint8_t permutation_index);

bool shuffled_dai_rd(uint32_t addr, uint32_t* rdata0, uint32_t* rdata1,
                     uint32_t granularity, uint32_t exp_status, uint8_t permutation_index) ;

bool calculate_digest_without_addr(uint32_t exp_status);

bool zeroize_without_addr(uint32_t exp_status);

// Returns true if addr is in the range of addresses that are visible
// to the Caliptra core but not the MCU.
bool is_caliptra_secret_addr(uint32_t addr);

#endif // FUSE_CTRL_H
