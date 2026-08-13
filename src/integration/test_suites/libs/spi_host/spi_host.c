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

void spi_host_write_control(spi_host_control_t control) {
  lsu_write_32(SOC_SPI_HOST_CONTROL, *(uint32_t *)&control);
}

void spi_host_write_config0(spi_host_config_opts_t config_opts) {
  lsu_write_32(SOC_SPI_HOST_CONFIGOPTS_0, *(uint32_t *)&config_opts);
}

void spi_host_write_config1(spi_host_config_opts_t config_opts) {
  lsu_write_32(SOC_SPI_HOST_CONFIGOPTS_1, *(uint32_t *)&config_opts);
}

void spi_host_write_command(spi_host_command_t command) {
  lsu_write_32(SOC_SPI_HOST_COMMAND, *(uint32_t *)&command);
}

void spi_host_write_tx_fifo(const uint32_t *data, size_t num_words) {
  for(uint8_t i = 0; i < num_words; i++) {
    // Check if TX FIFO is full before writing to it
    if (spi_host_read_status() & SPI_HOST_STATUS_TXFULL_MASK) {
      printf("TX FIFO is full ; Drain it first");
      return;
    }
    lsu_write_32(SOC_SPI_HOST_TXDATA, data[i]);
  }
}

void spi_host_write_csid(uint32_t csid) {
  lsu_write_32(SOC_SPI_HOST_CSID, csid);
}

void spi_host_wait_ready() {
  while (!(spi_host_read_status() & SPI_HOST_STATUS_READY_MASK));
}

void spi_host_wait_command_finish() {
  while (spi_host_read_status() & SPI_HOST_STATUS_ACTIVE_MASK);
}

uint32_t spi_host_read_rx_data() {
  return (lsu_read_32(SOC_SPI_HOST_RXDATA));
}

uint32_t spi_host_read_status() {
  return (lsu_read_32(SOC_SPI_HOST_STATUS));
}
