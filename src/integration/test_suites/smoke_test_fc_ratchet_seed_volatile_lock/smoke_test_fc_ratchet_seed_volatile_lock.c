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

static void expect_ratchet_seed_write(uint32_t partition_no, uint32_t wdata0, uint32_t wdata1,
                                      uint32_t exp_status, const char *msg) {
  uint32_t rdata[2];

  if (!dai_wr(partitions[partition_no].address, wdata0, wdata1,
              partitions[partition_no].granularity, exp_status)) {
    handle_error("ERROR: %s DAI write status mismatch\n", msg);
  }

  if (exp_status == 0) {
    dai_rd(partitions[partition_no].address, &rdata[0], &rdata[1],
           partitions[partition_no].granularity, 0);
    if (wdata0 != rdata[0] ||
        (partitions[partition_no].granularity > 32 && rdata[1] != wdata1)) {
      handle_error("ERROR: %s read_value does not match written_value\n", msg);
    }
  }
}

static void expect_ratchet_lock_reg(uint32_t expected, const char *msg) {
  uint32_t actual = lsu_read_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK);
  if (actual != expected) {
    handle_error("ERROR: %s expected 0x%08x actual 0x%08x\n", msg, expected, actual);
  }
}

static void check_ratchet_seed_unlocked_writes(void) {
  for (uint32_t partition_no = CPTRA_SS_LOCK_HEK_PROD_0;
       partition_no <= CPTRA_SS_LOCK_HEK_PROD_7; partition_no++) {
    expect_ratchet_seed_write(partition_no, 0xFF, 0xFF, 0,
                              "unlocked ratchet seed partition");
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
  for (uint32_t bit = 0; bit < 8; bit++) {
    const uint32_t partition_no = CPTRA_SS_LOCK_HEK_PROD_0 + bit;
    const uint32_t unlocked_partition = CPTRA_SS_LOCK_HEK_PROD_0 + ((bit + 1u) & 7u);
    const uint32_t lock_mask = 1u << bit;

    if (bit != 0) {
      reset_fc_for_next_case();
    }

    lsu_write_32(SOC_OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK, lock_mask);
    expect_ratchet_lock_reg(lock_mask, "ratchet seed volatile lock did not retain expected bit-mask");
    expect_ratchet_seed_write(unlocked_partition, 0xFF, 0xFF, 0,
                              "unselected ratchet seed partition");
    expect_ratchet_seed_write(partition_no, 0xFF, 0xFF, OTP_CTRL_STATUS_DAI_ERROR_MASK,
                              "locked ratchet seed partition");
  }
}

/**
   This tests takes the following steps:
   1 - Write read each ratchet seed while testing ratchet_seed_volatile_lock with the partition unlocked
   2 - calculates the digest, and resets the device
   3 - Writes read each ratchet seed now that partition is locked: all writes should fail
*/

void ratchet_seed_volatile_lock(void) {
  VPRINTF(LOW, "==================================\n");
  VPRINTF(LOW, "testing all ratchet seed registers \n");
  VPRINTF(LOW, "==================================\n\n");

  check_ratchet_seed_unlocked_writes();
  check_ratchet_lock_sticky_w1s();
  reset_fc_for_next_case();
  check_ratchet_volatile_lock_bits();

  VPRINTF(LOW, "==========================================\n");
  VPRINTF(LOW, "Before the digests have been calculated\n");
  VPRINTF(LOW, "==========================================\n");

  // Sticky W1S volatile locks clear only on reset, so reset before digest programming.
  reset_fc_for_next_case();
  for (uint32_t partition_no = CPTRA_SS_LOCK_HEK_PROD_0;
       partition_no <= CPTRA_SS_LOCK_HEK_PROD_7; partition_no++) {
    dai_wr(partitions[partition_no].digest_address, 0xFF, 0xFF, 32, 0);
  }
  VPRINTF(LOW, "==========================================\n");
  VPRINTF(LOW, "All the digests for HEKs partitions have been calculated\n");
  VPRINTF(LOW, "==========================================\n");

  reset_fc_for_next_case();

  VPRINTF(LOW, "==========================================\n");
  VPRINTF(LOW, "After after reset and DAI idle:\n");
  VPRINTF(LOW, "==========================================\n");

  // Digest lock coverage: each failure-expected DAI write is the final op before reset.
  for (uint32_t partition_no = CPTRA_SS_LOCK_HEK_PROD_0;
       partition_no <= CPTRA_SS_LOCK_HEK_PROD_7; partition_no++) {
    expect_ratchet_seed_write(partition_no, 0xFF, 0xFF, OTP_CTRL_STATUS_DAI_ERROR_MASK,
                              "digest-locked ratchet seed partition");
    if (partition_no < CPTRA_SS_LOCK_HEK_PROD_7) {
      reset_fc_for_next_case();
    }
  }

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
