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

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "spi_host.h"
#include <stddef.h>
#include <stdlib.h>
#include <stdbool.h>

#define ARRAY_SIZE(arr) (sizeof(arr) / sizeof((arr)[0]))
#define PAGE_PROGRAM_WRITE_OPC 0x2
#define QUAD_READ_OPC 0x6B
#define PAGE_SIZE 256u
#define FIFO_DEPTH 64u

volatile char *stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

struct command_segment_fields_s {
  uint32_t opcode;
  uint32_t flash_addr;
  uint32_t data[FIFO_DEPTH];
};

struct command_segment_fields_s setup_segment_fields(uint32_t opcode) {
  struct command_segment_fields_s segment_fields = { .opcode = opcode };

  // SPI Flash is 1MB consist of 4096 pages with a page size of 256B. SPI Flash model use LSB byte
  // of flash_addr as the page offset. This test will write 256B to the flash so ensure the last
  // byte of the flash_addr points to the start of the page.
  segment_fields.flash_addr = (rand() % 0x100000) & 0xFFF00u;

  for (uint8_t i = 0; i < FIFO_DEPTH; i++) {
    segment_fields.data[i] = rand();
  }

  return segment_fields;
}

bool compare_rx_bytes(const uint32_t *data, size_t num_words) {
  for (uint8_t i = 0; i < num_words; i++) {
    uint32_t rx_data = spi_host_read_rx_data();
    if (data[i] != rx_data) {
      VPRINTF(LOW, "[Mismatch] - Expecting 0x%0x ; Got 0x%0x", data[i], rx_data);
      return false;
    }
  }
  return true;
}

uint8_t tx_rx_bytes(uint8_t csid, const spi_host_command_t *command, uint8_t num_segments) {
  struct command_segment_fields_s segment_fields = setup_segment_fields(PAGE_PROGRAM_WRITE_OPC);

  spi_host_write_tx_fifo(&segment_fields.opcode, 0x1u);
  spi_host_write_tx_fifo(&segment_fields.flash_addr, 0x1u);
  spi_host_write_tx_fifo(&segment_fields.data[0], FIFO_DEPTH);

  segment_fields.opcode = QUAD_READ_OPC;
  spi_host_write_tx_fifo(&segment_fields.opcode, 0x1u);
  spi_host_write_tx_fifo(&segment_fields.flash_addr, 0x1u);

  spi_host_write_csid(csid);

  VPRINTF(LOW,
          "[FLASH%0d] TX / RX %0dB to / from page 0x%0x",
          csid, (FIFO_DEPTH * 4), (segment_fields.flash_addr >> 8u));

  for (uint32_t i = 0; i < num_segments; i++) {
    spi_host_wait_ready();
    spi_host_write_command(command[i]);
  }

  spi_host_wait_command_finish();

  if (!(compare_rx_bytes(&segment_fields.data[0], FIFO_DEPTH))) {
    return 1;
  }

  return 0;
}

uint8_t main() {
  spi_host_config_opts_t config_opts = { .cpha = 0, .cpol = 0 };
  spi_host_control_t control = { .output_en = 1, .spien = 1 };
  uint8_t num_bytes = (FIFO_DEPTH * 4u) - 1u;

  // The sequence of the commands looks like:
  // For write command:
  // Segment1 : SPI Host sends 8b opcode PAGE_PROGRAM_WRITE_OPC in standard mode
  // Segment2 : SPI Host sends 3B address in quad mode
  // Segment3 : SPI Host sends data bytes of length num_bytes.
  // Communications terminates after Segment 3.
  // For read command:
  // Segment1 : SPI Host sends 8b opcode QUAD_READ_OPC in standard mode
  // Segment2 : SPI Host sends 3B address in quad mode
  // Segment3 : SPI Host adds 2 dummy cycles
  // Segment4 : SPI Host receives data bytes of length num_bytes from SPI Flash in quad mode
  spi_host_command_t command[7] = { // Write command's segments:
                                   {.csaat = 0x1, .speed = std,  .direction = tx, .len = 0x0},
                                   {.csaat = 0x1, .speed = quad, .direction = tx, .len = 0x2},
                                   {.csaat = 0x0, .speed = std,  .direction = tx, .len = num_bytes},
                                    // Read command's segments
                                   {.csaat = 0x1, .speed = std,  .direction = tx,   .len = 0x0},
                                   {.csaat = 0x1, .speed = quad, .direction = tx,   .len = 0x2},
                                   {.csaat = 0x1, .speed = std,  .direction = none, .len = 0x1},
                                   {.csaat = 0x0, .speed = quad, .direction = rx,   .len = num_bytes}
                                  };

  spi_host_write_control(control);
  spi_host_write_config0(config_opts);
  spi_host_write_config1(config_opts);

  return (tx_rx_bytes(0x0, command, ARRAY_SIZE(command)) |
          tx_rx_bytes(0x1, command, ARRAY_SIZE(command)));
}
