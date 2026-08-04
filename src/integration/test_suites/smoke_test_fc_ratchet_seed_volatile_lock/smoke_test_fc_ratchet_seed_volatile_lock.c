//********************************************************************************
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
//********************************************************************************
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"
#include "fuse_ctrl_mmap.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif




static void reset_fc_for_next_case(void) {
  reset_fc_lcc_rtl();
  wait_dai_op_idle(0);
  grant_mcu_for_fc_writes();
}

static void expect_ratchet_lock_reg(uint32_t expected, const char *msg) {
  uint32_t actual = lsu_read_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK);
  if (actual != expected) {
    handle_error("ERROR: %s expected 0x%08x actual 0x%08x\n", msg, expected, actual);
  }
}

static void check_ratchet_lock_sticky_w1s(void) {
  uint32_t lock_mask = 0;

  for (uint32_t bit = 0; bit < 8; bit++) {
    lock_mask |= (1u << bit);
    lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 1u << bit);
    expect_ratchet_lock_reg(lock_mask, "ratchet seed volatile lock did not accumulate bit-mask");
    lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 0);
    expect_ratchet_lock_reg(lock_mask, "writing 0 cleared sticky ratchet seed volatile lock bits");
  }
}

static void check_ratchet_volatile_lock_bits(void) {
  // Sticky accumulation: each iteration leaves the prior bits locked, so a
  // successful marker write to partition i also proves the already-engaged locks
  // for bits < i do not block it (selectivity), while the complement read-back
  // proves bit i blocks partition i. Each partition is the marker target exactly
  // once, so every entry is still blank when its marker is programmed.
  for (uint32_t bit = 0; bit < 8; bit++) {
    const uint32_t partition_no = CPTRA_SS_LOCK_HEK_PROD_0 + bit;

    if (!dai_lock_blocks_write(partitions[partition_no].address,
                               partitions[partition_no].granularity,
                               SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, 1u << bit)) {
      handle_error("ERROR: locked ratchet seed partition %u was modified despite the volatile lock\n",
                   bit);
    }
  }
  expect_ratchet_lock_reg(0xFFu, "ratchet seed volatile lock did not accumulate all eight bits");
}

/**
   Exercises the ratchet seed volatile lock:
   1 - Sticky W1S behaviour of the lock CSR (write 0 does not clear set bits).
   2 - Each lock bit blocks writes to its ratchet seed partition (per-bit, with
       sticky accumulation proving selectivity), verified by data read-back.

   Note: digest-based locking of these partitions is a separate mechanism that is
   covered by the digest/zeroization tests (e.g. smoke_test_fc_ratchet_seed_lock_en,
   smoke_test_fc_ocp_lock_zeroization), so it is intentionally not retested here.
*/

void ratchet_seed_volatile_lock(void) {
  VPRINTF(LOW, "==================================\n");
  VPRINTF(LOW, "testing all ratchet seed registers \n");
  VPRINTF(LOW, "==================================\n\n");

  check_ratchet_lock_sticky_w1s();
  reset_fc_for_next_case();
  check_ratchet_volatile_lock_bits();

  VPRINTF(LOW, "Ratchet seed volatile lock test finished\n");
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    lcc_initialization();
    grant_mcu_for_fc_writes();

    initialize_otp_controller();

    VPRINTF(LOW, "=================\nBefore ratchet_seed_volatile_lock\n=================\n\n");
    ratchet_seed_volatile_lock();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
