//********************************************************************************
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
//********************************************************************************

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "caliptra_ss_clk_freq.h"
#include <string.h>
#include <stdint.h>

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void uart_tx(uint8_t data) {
  uint32_t status, tx_full;
  VPRINTF(LOW, "uart_tx >> Sending 0x%x\n", data);
  // Check the TX fifo is not full
  do {
    status = lsu_read_32(SOC_UART_STATUS);
    tx_full = status & UART_STATUS_TXFULL_MASK;
  } while (tx_full);

  lsu_write_32(SOC_UART_WDATA, data);
}

uint8_t uart_rx() {
  uint32_t status, rx_empty, data;

  // Check the RX fifo is empty
  do {
    status = lsu_read_32(SOC_UART_STATUS);
    rx_empty = status & UART_STATUS_RXEMPTY_MASK;
  } while (rx_empty);

  // read the data
  data = lsu_read_32(SOC_UART_RDATA);
  VPRINTF(LOW, "uart_rx << Receiving 0x%x\n", data);
  return data & 0xff;
}

int run_loopback_test() {
  int errors = 0;
  uint8_t rxdata, txdata;

  for (int ii = 0; ii < 10; ii++) {
    txdata = 3 * ii + 7;
    uart_tx(txdata);

    rxdata = uart_rx();

    if (rxdata != txdata) {
      VPRINTF(LOW, "run_loopback_test: Got: 0x%x Want: 0x%x\n", rxdata, txdata);
      errors += 1;
    }
  }

  return errors;
}

uint8_t main (void) {
    uint32_t v;
    int errors;

    VPRINTF(LOW, "---------------------------\n");
    VPRINTF(LOW, "UART Smoke Test\n");
    VPRINTF(LOW, "---------------------------\n");

    uint64_t clock_freq_hz = CALIPTRA_SS_CLK_FREQ * 1000 * 1000;
    uint64_t target_baud = 1000000;
    uint32_t nco = (uint32_t)((target_baud << 20) / clock_freq_hz);

    VPRINTF(LOW, "Clock: %u MHz, Target baud rate: %u\n", CALIPTRA_SS_CLK_FREQ, target_baud);
    VPRINTF(LOW, "UART NCO: %u\n", nco);

    // The testbench is configured for loopback, so there is no need to set LLPBK or SLPBK.
    v = (nco << UART_CTRL_NCO_LOW) | UART_CTRL_TX_MASK | UART_CTRL_RX_MASK;
    lsu_write_32(SOC_UART_CTRL, v);

    VPRINTF(LOW, "Start loopback test\n");

    errors = run_loopback_test();
    if (errors) {
        VPRINTF(ERROR, "Error: %d\n", errors);
        return 1;
    }

    // success
    return 0;
}
