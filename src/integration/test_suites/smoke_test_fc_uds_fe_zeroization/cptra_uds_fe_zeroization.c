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
//
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "fuse_ctrl_mmap.h"
#include "printf.h"
#include "riscv-csr.h"
#include "riscv_hw_if.h"
#include "soc_address_map.h"
#include "soc_ifc.h"
#include "veer-csr.h"

volatile uint32_t* stdout = (uint32_t*)STDOUT;
volatile uint32_t intr_count = 0;
#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif
volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define LOG_ERROR(...) VPRINTF(LOW, "CLP_CORE ERROR:" #__VA_ARGS__)
#define LOG_INFO(...) VPRINTF(LOW, "CLP_CORE:" #__VA_ARGS__)

static inline void sleep(const uint32_t cycles) {
  for (uint8_t ii = 0; ii < cycles; ii++) {
    __asm__ volatile("nop");
  }
}

#define FUSE_CTRL_CMD_DAI_ZER 0x8
#define FUSE_CTRL_CMD_DAI_WRITE 0x2
#define FUSE_CTRL_CMD_DAI_READ 0x1

static uint32_t dma_read_from_lsu(uint32_t address) {
  uint32_t read_data;
  soc_ifc_axi_dma_read_ahb_payload(address, 0, &read_data, 4, 0);
  return read_data;
}

static void dma_write_from_lsu(uint32_t address, uint32_t write_data) {
  soc_ifc_axi_dma_send_ahb_payload(address, 0, &write_data, 4, 0);
}

void dma_wait_dai_op_idle(uint32_t status_mask) {
  uint32_t status;
  uint32_t dai_idle;
  uint32_t check_pending;

  const uint32_t error_mask = OTP_CTRL_STATUS_DAI_IDLE_MASK - 1;

  VPRINTF(LOW, "DEBUG: Waiting for DAI to become idle...\n");
  do {
    status = dma_read_from_lsu(SOC_OTP_CTRL_STATUS);
    dai_idle = (status >> OTP_CTRL_STATUS_DAI_IDLE_LOW) & 0x1;
    check_pending = (status >> OTP_CTRL_STATUS_CHECK_PENDING_LOW) & 0x1;
  } while ((!dai_idle || check_pending) &&
           ((status & error_mask) != error_mask));

  // Clear the IDLE bit from the status value
  status &= ((((uint32_t)1) << (OTP_CTRL_STATUS_DAI_IDLE_LOW - 1)) - 1);
  if ((status & error_mask) != status_mask) {
    VPRINTF(LOW, "ERROR: unexpected status: expected: %08X actual: %08X\n",
            status_mask, status);
    lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP,
                 SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_FAIL_MASK);

    // End the test.
    SEND_STDOUT_CTRL(0xff);
  }
  VPRINTF(LOW, "DEBUG: DAI is now idle.\n");
  return;
}

void dma_dai_wr(uint32_t addr, uint32_t wdata0, uint32_t wdata1,
                uint32_t granularity, uint32_t exp_status) {
  VPRINTF(LOW, "CLP_CORE: Starting DAI write operation...\n");

  VPRINTF(LOW, "CLP_CORE: Writing wdata0: 0x%08X to DIRECT_ACCESS_WDATA_0.\n",
          wdata0);
  dma_write_from_lsu(SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_0, wdata0);

  if (granularity == 64) {
    VPRINTF(LOW, "CLP_CORE: Writing wdata1: 0x%08X to DIRECT_ACCESS_WDATA_1.\n",
            wdata1);
    dma_write_from_lsu(SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_1, wdata1);
  }

  VPRINTF(LOW, "CLP_CORE: Writing address: 0x%08X to DIRECT_ACCESS_ADDRESS.\n",
          addr);
  dma_write_from_lsu(SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS, addr);

  VPRINTF(LOW, "CLP_CORE: Triggering DAI write command.\n");
  dma_write_from_lsu(SOC_OTP_CTRL_DIRECT_ACCESS_CMD, FUSE_CTRL_CMD_DAI_WRITE);

  dma_wait_dai_op_idle(exp_status);
}

static void dma_dai_rd(uint32_t addr, uint32_t* rdata0, uint32_t* rdata1,
                       uint32_t granularity, uint32_t exp_status) {
  VPRINTF(LOW, "CLP_CORE: Starting DAI read operation...\n");

  VPRINTF(LOW, "CLP_CORE: Writing address: 0x%08X to DIRECT_ACCESS_ADDRESS.\n",
          addr);
  dma_write_from_lsu(SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS, addr);

  VPRINTF(LOW, "CLP_CORE: Triggering DAI read command.\n");
  dma_write_from_lsu(SOC_OTP_CTRL_DIRECT_ACCESS_CMD, FUSE_CTRL_CMD_DAI_READ);

  dma_wait_dai_op_idle(exp_status);

  *rdata0 = dma_read_from_lsu(SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_0);
  VPRINTF(LOW, "CLP_CORE: Read data from DIRECT_ACCESS_RDATA_0: 0x%08X\n",
          *rdata0);

  if (granularity == 64) {
    *rdata1 =
        dma_read_from_lsu(SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_1);
    VPRINTF(LOW, "CLP_CORE: Read data from DIRECT_ACCESS_RDATA_1: 0x%08X\n",
            *rdata1);
  }
}

void dma_dai_zer(uint32_t addr, uint32_t* rdata0, uint32_t* rdata1,
                 uint32_t granularity, uint32_t exp_status) {
  VPRINTF(LOW, "CLP_CORE: Starting DAI zeroization operation...\n");

  VPRINTF(LOW, "CLP_CORE: Writing address: 0x%08X to DIRECT_ACCESS_ADDRESS.\n",
          addr);
  dma_write_from_lsu(SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS, addr);

  VPRINTF(LOW, "CLP_CORE: Triggering DAI write command.\n");
  dma_write_from_lsu(SOC_OTP_CTRL_DIRECT_ACCESS_CMD, FUSE_CTRL_CMD_DAI_ZER);

  dma_wait_dai_op_idle(exp_status);

  *rdata0 = dma_read_from_lsu(SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_0);
  VPRINTF(LOW, "CLP_CORE: Read data from DIRECT_ACCESS_RDATA_0: 0x%08X\n",
          *rdata0);

  if (granularity == 64) {
    *rdata1 =
        dma_read_from_lsu(SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_1);
    VPRINTF(LOW, "CLP_CORE: Read data from DIRECT_ACCESS_RDATA_1: 0x%08X\n",
            *rdata1);
  }
}

static uint32_t zeroize_partition(uint32_t partition_id) {
  enum {
    kPass = SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_MASK,
    kFail = SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_FAIL_MASK,
  };

  if (partition_id >= NUM_PARTITIONS) {
    return kFail;
  }

  partition_t* p = &partitions[partition_id];
  const uint32_t kGranularity = p->granularity / CHAR_BIT;
  uint32_t read_data[2];

  // Check if the partition supports zeroization by checking the offset to the
  // zeroize flag, which must be neq zero.
  if (p->zer_address == 0) {
    VPRINTF(LOW, "ERROR: partition_id: %d has no zeroize marker\n",
            partition_id);
    return kFail;
  }

  // Read the digest to determine if the partition is locked. Read via DAI to
  // avoid having to calculate the digest register offset.
  dma_dai_rd(p->digest_address, &read_data[0], &read_data[1], 64, 0);
  if (read_data[0] == 0 && read_data[1] == 0) {
    VPRINTF(LOW, "ERROR: partition_id: %d is NOT locked\n", partition_id);
    return kFail;
  }

  // Zeroize marker field.
  dma_dai_zer(p->zer_address, &read_data[0], &read_data[1], 64, 0);
  if (read_data[0] != 0xFFFFFFFF || read_data[1] != 0xFFFFFFFF) {
    VPRINTF(LOW, "ERROR: partition_id: %d marker is not zeroized\n",
            partition_id);
    return kFail;
  }

  // Zeroize fuse fields.
  for (uint32_t addr = p->address; addr < p->digest_address;
       addr += kGranularity) {
    dma_dai_zer(addr, &read_data[0], &read_data[1], p->granularity, 0);
    if (read_data[0] != 0xFFFFFFFF ||
        (kGranularity > sizeof(uint32_t) && read_data[1] != 0xFFFFFFFF)) {
      VPRINTF(LOW,
              "ERROR: fuse at addr 0x%08X is not zeroized, got: 0x%08X%08X\n",
              addr, read_data[1], read_data[0]);
      return kFail;
    }
  }

  // Zeroize digest field.
  dma_dai_zer(p->digest_address, &read_data[0], &read_data[1], 64, 0);
  if (read_data[0] != 0xFFFFFFFF || read_data[1] != 0xFFFFFFFF) {
    VPRINTF(LOW, "ERROR: partition_id: %d digest is not zeroized\n",
            partition_id);
    return kFail;
  }

  return kPass;
}

void main(void) {
  VPRINTF(LOW, "Caliptra: Mimicking ROM from Subsystem!!\n");

  // Service zeroization requests.
  while (1) {
    uint32_t status_reg = lsu_read_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ);
    if (status_reg == SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_UDS_PROGRAM_REQ_MASK) {
      VPRINTF(LOW, "CLP_CORE: detected zeroization request\n");

      // Clear the request.
      status_reg &= (SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_UDS_PROGRAM_REQ_MASK ^
                     0xFFFFFFFF);
      lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ, status_reg);

      status_reg =
          lsu_read_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP) |
          SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_MASK;
      VPRINTF(LOW, "CLP_CORE: Zeroization IN_PROGRESS\n");
      lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP, status_reg);

      // Get the partition ID from the UDS Low Address Register.
      uint32_t partition_id =
          lsu_read_32(CLP_SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_L);

      uint32_t result = zeroize_partition(partition_id);

      // Set the result of the operation, while clearing any previous status not
      // cleared by the caller.
      status_reg = lsu_read_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP);
      status_reg &=
          ((SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_MASK |
            SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_MASK |
            SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_FAIL_MASK) ^
           0xFFFFFFFF);
      status_reg |= result;

      VPRINTF(LOW, "CLP_CORE: Zeroization complete. Result: 0x%08X\n",
              status_reg);
      lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP, status_reg);
    }
    sleep(100);
  }
}
