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

#include <stdint.h>
#include <stddef.h>

typedef struct {
  uint32_t rx_watermark : 8;
  uint32_t tx_watermark : 8;
  uint32_t : 13;
  uint32_t output_en : 1;
  uint32_t sw_rst : 1;
  uint32_t spien : 1;
} spi_host_control_t;

typedef struct {
  uint32_t clkdiv : 16;
  uint32_t csnidle : 4;
  uint32_t csntrail : 4;
  uint32_t csnlead : 4;
  uint32_t : 1;
  uint32_t fullcyc : 1;
  uint32_t cpha : 1;
  uint32_t cpol : 1;
} spi_host_config_opts_t;

typedef struct {
  uint32_t len : 9;
  uint32_t csaat : 1;
  uint32_t speed : 2;
  uint32_t direction : 2;
  uint32_t : 18;
} spi_host_command_t;

enum __attribute__((packed)) {
  none = 0x0,
  rx = 0x1,
  tx = 0x2,
  bidir = 0x3,
};

enum __attribute__((packed)) {
  std = 0x0,
  dual = 0x1,
  quad = 0x2,
};

void spi_host_write_control(spi_host_control_t control);
void spi_host_write_config0(spi_host_config_opts_t config_opts);
void spi_host_write_config1(spi_host_config_opts_t config_opts);
void spi_host_write_command(spi_host_command_t command);
void spi_host_write_tx_fifo(const uint32_t *data, size_t num_words);
void spi_host_write_csid(uint32_t csid);
void spi_host_wait_ready();
void spi_host_wait_command_finish();
uint32_t spi_host_read_rx_data();
uint32_t spi_host_read_status();
