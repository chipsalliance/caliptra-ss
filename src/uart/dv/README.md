# Caliptra SS UART DV Document

## Goals
* **DV**
  * Verify all Caliptra Subsystem (`caliptra-ss`) UART IP features and its AXI4 subordinate wrapper (`uart_axi`) by running dynamic simulations with a SystemVerilog/UVM-based testbench.
  * Develop and run all tests based on the [testplan](#testplan) below towards closing code, assertion, and functional coverage on the IP and all of its sub-modules.
* **Assertions / Protocol Compliance**
  * Verify AXI4 subordinate interface behavior, internal TileLink-UL protocol compliance (`tlul_assert`), and security countermeasures (bus command/data SECDED integrity and one-hot register write-enable checks) via SVA assertions.

## Design Features
For detailed information on Caliptra SS UART design features, please see the [UART design specification](../README.md).
Key hardware parameters in `caliptra-ss`:
* **External Bus Interface:** AXI4 Subordinate (`uart_axi` wrapping `axi2tlul` and `caliptra_ss_uart`)
* **Serial Interface:** 2-pin full-duplex asynchronous UART (`cio_rx_i`, `cio_tx_o`, `cio_tx_en_o`)
* **FIFOs:** 32-byte TX FIFO and 32-byte RX FIFO (`caliptra_prim_fifo_sync`)
* **Interrupts:** 9 interrupt lines (`tx_watermark`, `rx_watermark`, `tx_done`, `rx_overflow`, `rx_frame_err`, `rx_break_err`, `rx_timeout`, `rx_parity_err`, `tx_empty`)

## Testbench Architecture
The Caliptra SS UART testbench is constructed on top of the `caliptra-ss` DV library (`dv_lib_pkg`, `csr_utils_pkg`, `dv_utils_pkg`) and uses an AXI4 Manager VIP agent (`axi_agent`) to drive register and FIFO accesses into the `uart_axi` DUT.

### Top-Level Testbench
The top-level testbench is located at `src/uart/dv/tb/tb.sv`. It instantiates the top-level AXI-wrapped UART DUT module `uart_axi` (`src/uart/rtl/uart_axi.sv`), which integrates:
* `axi2tlul` (`src/axi2tlul/rtl/axi2tlul.sv`): AXI4 subordinate (`axi_sub`) and AXI-to-TLUL shim (`sub2tlul`) with SECDED command/data integrity generation (`axi2tlul_cmd_intg_gen`).
* `caliptra_ss_uart` (`src/uart/rtl/uart.sv`): UART register block (`caliptra_ss_uart_reg_top`) and UART core (`caliptra_ss_uart_core`, `caliptra_ss_uart_tx`, `caliptra_ss_uart_rx`).

In addition, `tb.sv` instantiates the following interfaces, connects them to the DUT, and registers their virtual interface handles in `uvm_config_db`:
* **Clock and reset interface:** `clk_rst_if` (`third_party/caliptra-rtl/tools/dv-classes/common_ifs/clk_rst_if.sv`)
* **AXI4 subordinate interfaces:** `axi_if`, `axi_read_request_if`, `axi_read_data_if`, `axi_write_request_if`, `axi_write_data_if`, and `axi_write_response_if` (`tools/dv-classes/axi_agent/`)
* **UART serial I/O interface:** `uart_if` (`tools/dv-classes/uart_agent/uart_if.sv`)
* **Interrupt pins interface:** `pins_if #(NUM_INTRS)` (`third_party/caliptra-rtl/tools/dv-classes/common_ifs/pins_if.sv`)
* **Security countermeasure & internal monitor interfaces:** `uart_sec_cm_if`, `uart_intg_error_if`, and `uart_nf_if` (`src/uart/dv/env/`)

### Common DV Utility Components
The following shared packages provide generic base classes, register access utilities, and helper macros across `caliptra-ss`:
* `common_ifs` (`third_party/caliptra-rtl/tools/dv-classes/common_ifs`)
* `dv_utils_pkg` (`third_party/caliptra-rtl/tools/dv-classes/dv_utils`)
* `csr_utils_pkg` (`third_party/caliptra-rtl/tools/dv-classes/csr_utils`)
* `dv_lib_pkg` (`third_party/caliptra-rtl/tools/dv-classes/dv_lib`)

### Global Types & Methods
All common types, watermark/break helper functions, and parameters (`MAX_RX_WATERMARK_LVL`, `MAX_TX_WATERMARK_LVL`, `NUM_INTRS`, `uart_intr_e`) are defined in `uart_env_pkg` (`src/uart/dv/env/uart_env_pkg.sv`).

### AXI Agent
`uart_env` instantiates `axi_mgr_agent` (`tools/dv-classes/axi_agent`), which drives and independently monitors AXI4 read and write transactions across all 5 AXI channels (`AR`, `R`, `AW`, `W`, `B`). It is paired with `axi_reg_adapter` to translate UVM RAL operations into AXI4 bus transactions.

### UART Agent
`uart_agent` (`tools/dv-classes/uart_agent`) is used to drive and monitor serial UART RX/TX transactions and collect serial functional coverage on direction, data, parity, baud rate, and mid-transfer resets.
Supported baud rates (`baud_rate_e`) include: `9600`, `115200`, `230400`, `1Mbps (1048576)`, and `1.5Mbps (1500000)`.

### UVM RAL Model
The UART UVM RAL model (`uart_reg_block`) is defined in `src/uart/dv/ral/uart_ral_pkg.sv` (generated from `src/uart/data/uart.hjson`) and compiled via FuseSoC core `lowrisc:dv:uart_ral_pkg`.

### Stimulus Strategy
#### Test Sequences
All virtual test sequences reside in `src/uart/dv/env/seq_lib/` and extend `uart_base_vseq` (`src/uart/dv/env/seq_lib/uart_base_vseq.sv`).
Commonly used tasks in `uart_base_vseq` include:
* `uart_init`: Configures UART control, baud rate (`NCO`), interrupt enable, timeout, and FIFO watermark CSRs with randomized values.
* `send_tx_byte`: Writes a byte to `WDATA` over AXI to transmit a serial frame on `cio_tx_o`.
* `send_rx_byte` / `drive_rx_error_byte`: Drives a serial byte (with optional parity or framing error) onto `cio_rx_i` via `uart_agent`.

Key test sequences in `src/uart/dv/env/seq_lib/`:
* `uart_smoke_vseq`: Basic TX and RX byte transmission, reception, and status verification.
* `uart_tx_rx_vseq`: Concurrent randomized full-duplex TX/RX transfers with random inter-byte and CSR polling delays.
* `uart_fifo_full_vseq`: Fills TX and RX FIFOs to capacity (32 bytes) and drains them.
* `uart_fifo_overflow_vseq`: Drives beyond 32 bytes to verify RX/TX FIFO overflow behavior and `rx_overflow` interrupt.
* `uart_fifo_reset_vseq`: Exercises `FIFO_CTRL.RXRST` and `FIFO_CTRL.TXRST` across all FIFO fill levels.
* `uart_intr_vseq`: Exhaustively verifies all 9 UART interrupts (`tx_watermark`, `rx_watermark`, `tx_done`, `rx_overflow`, `rx_frame_err`, `rx_break_err`, `rx_timeout`, `rx_parity_err`, `tx_empty`), including line break detection across all programmable break character levels (`RXBLVL`: 2, 4, 8, 16 chars).
* `uart_rx_parity_err_vseq`: Verifies even and odd parity checking and `rx_parity_err` assertion.
* `uart_rx_oversample_vseq`: Tests 16x oversampling and `VAL` register capture.
* `uart_noise_filter_vseq` & `uart_rx_start_bit_filter_vseq`: Verifies 3-sample majority noise filtering and start-bit glitch rejection.
* `uart_tx_ovrd_vseq`: Verifies direct TX pin override control via `OVRD.TXEN` and `OVRD.TXVAL`.
* `uart_loopback_vseq`: Verifies both system loopback (`CTRL.SLPBK`) and line loopback (`CTRL.LLPBK`).
* `uart_perf_vseq` & `uart_long_xfer_wo_dly_vseq`: Back-to-back streaming performance and zero-delay transfers.
* `uart_reg_access_err_vseq` & `uart_sec_cm_vseq`: Verifies AXI error responses (`SLVERR`), unmapped/sub-word accesses, and TileLink command/data SECDED integrity fault injection.
* `uart_axi_toggle_vseq`: Exercises AXI4 burst types (`FIXED`, `INCR`, `WRAP`), burst lengths, transfer sizes, stall cycles, and address/data bus toggles.
* `uart_stress_all_vseq` & `uart_stress_all_with_rand_reset_vseq`: Runs randomized combinations of all sequences with and without asynchronous hardware resets (`rst_ni`).
* `uart_common_vseq`: Runs automated CSR verification suites (`csr_hw_reset`, `csr_rw`, `csr_bit_bash`, `csr_aliasing`, `same_csr_outstanding`, and `intr_test`).

#### Functional Coverage
Functional coverage is collected across 16 covergroups in the AXI monitors, UART agent, and UART environment:
* **AXI4 Channel Covergroups (`tools/dv-classes/axi_agent/`):**
  * `ar_cg` (`axi_monitor_ar.svh`) & `aw_cg` (`axi_monitor_aw.svh`): Burst type (`FIXED`, `INCR`, `WRAP`), burst size, burst length, lock, handshake stall cycles, and `cx_burst_len` cross.
  * `w_cg` (`axi_monitor_w.svh`): Write strobes (`wstrb`), `wlast`, and stall cycles.
  * `b_cg` (`axi_monitor_b.svh`) & `r_cg` (`axi_monitor_r.svh`): Response status (`OKAY`, `SLVERR`), `rlast`, and stall cycles.
* **UART Agent Covergroups (`tools/dv-classes/uart_agent/uart_agent_cov.sv`):**
  * `uart_cg`: Direction (`UartTx`, `UartRx`), data byte values, parity enable/odd-even mode, and baud rate.
  * `uart_reset_cg`: Asynchronous reset across every bit position (start, 8 data, parity, stop) for both TX and RX.
* **UART Environment Covergroups (`src/uart/dv/env/uart_env_cov.sv`):**
  * `rx_fifo_level_cg` & `tx_fifo_level_cg`: All RX/TX FIFO occupancy levels (`0..32`) crossed with FIFO reset.
  * `baud_rate_w_core_clk_cg`: Cross of all supported baud rates and core clock frequencies.
  * `tx_watermark_cg` & `rx_watermark_cg`: All TX and RX watermark interrupt levels.
  * `rx_break_err_cg`: Break interrupt across all 4 `RXBLVL` settings (`0..3`).
  * `rx_timeout_cg`: RX timeout interrupt across small, medium, and large timeout values.
  * `rx_parity_err_cg`: Parity error interrupt across even and odd parity modes.
  * `noise_filter_cg`: All 3-bit majority noise filter sample combinations.

### Self-Checking Strategy
#### Scoreboard
`uart_scoreboard` (`src/uart/dv/env/uart_scoreboard.sv`) performs cycle-accurate end-to-end checking:
* **AXI4 Analysis FIFOs (`aw_fifo`, `w_fifo`, `b_fifo`, `ar_fifo`, `r_fifo`):** Reconstructs AXI4 read and write transactions, updates the RAL mirror, models TX/RX FIFO state, and verifies `OKAY`/`SLVERR` bus responses.
* **UART Serial Analysis FIFOs (`uart_tx_fifo`, `uart_rx_fifo`):** Compares transmitted serial frames against `WDATA` writes, predicts `RDATA` reads from received serial frames (accounting for loopback, noise filtering, parity/framing errors, and FIFO resets), and checks all 9 interrupt pins and `INTR_STATE` bits.

#### Assertions
* **TL-UL Protocol Assertions:** `src/uart/dv/sva/uart_bind.sv` binds `tlul_assert` (`src/tlul/rtl/tlul_assert.sv`) to the internal `caliptra_ss_uart` TileLink-UL interface.
* **RTL Assertions:** `caliptra_prim_assert.sv` assertions inside the RTL verify that all outputs are known (`!X`) out of reset, FIFO pointers/depths remain within bounds, and register write-enables are one-hot.

## Building and Running Tests
Tests and regressions are built and executed using `tools/dvsim/dvsim.py` and the configuration file `src/uart/dv/uart_sim_cfg.hjson`:

* **Run a single test (e.g. `uart_smoke`):**
  ```console
  $ ./tools/dvsim/dvsim.py src/uart/dv/uart_sim_cfg.hjson -i uart_smoke
  ```
* **Run the smoke regression:**
  ```console
  $ ./tools/dvsim/dvsim.py src/uart/dv/uart_sim_cfg.hjson -i smoke
  ```
* **Run the full regression with code and functional coverage:**
  ```console
  $ ./tools/dvsim/dvsim.py src/uart/dv/uart_sim_cfg.hjson --cov
  ```

### Coverage Configuration & Exclusions
* **Compile-time hierarchy configuration (`-cm_hier`):** `src/uart/dv/cov/uart_cover.cfg`
* **Coverage exclusion file (`-elfile`):** `src/uart/dv/cov/uart_cov_excl.el`

## Testplan
* [UART Testplan](../data/uart_testplan.hjson)
* [UART Security Countermeasures Testplan](../data/uart_sec_cm_testplan.hjson)
