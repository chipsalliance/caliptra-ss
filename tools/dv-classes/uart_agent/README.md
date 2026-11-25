# UART Agent

Reusable UVM Verification IP (`uart_agent_pkg`) for driving, monitoring,
logging, and collecting functional coverage on asynchronous UART serial lines
(`uart_rx` / `uart_tx`).

## Architecture & Components

*   **`uart_if` (`uart_if.sv`)**: Serial interface carrying `uart_rx`,
    `uart_tx`, internal `uart_rx_clk` / `uart_tx_clk` sampling clocks derived
    from `uart_clk_period`, pulse counters, idle wait helpers
    (`wait_for_tx_idle`, `wait_for_rx_idle`, `wait_for_idle`), and glitch
    injection (`drive_uart_rx_glitch`).
*   **`uart_item` (`uart_item.sv`)**: Transaction item representing a single
    UART frame (`start_bit`, 8-bit `data`, optional `parity` and
    `ovrd_en_parity`, `stop_bit`, and error flags).
*   **`uart_agent_cfg` (`uart_agent_cfg.sv`)**: Configuration object holding the
    virtual interface handle (`vif`), baud rate, parity settings, monitor and
    checker enables, glitch/drift controls, logger options, and reset
    notification hooks.
*   **`uart_driver` (`uart_driver.sv`)**: Active RX driver that serializes
    `uart_item` frames onto `uart_rx`, injects optional edge glitches
    (`uart_period_glitch_pct`), and aborts cleanly to idle-high (`uart_rx = 1`)
    when `cfg.in_reset` is asserted.
*   **`uart_monitor` (`uart_monitor.sv`)**: Passive full-duplex TX and RX
    monitor publishing decoded frames on `tx_analysis_port` and
    `rx_analysis_port`, with configurable start/parity/stop-bit checks and
    baud-drift timing checks.
*   **`uart_sequencer` (`uart_sequencer.sv`)** and **`seq_lib/`**: UVM sequencer
    and reusable RX frame sequence (`uart_seq`) supporting normal, parity-error,
    and framing-error stimulus.
*   **`uart_agent_cov` (`uart_agent_cov.sv`)**: Protocol covergroups sampled
    when `cfg.en_cov` is enabled.
*   **`uart_logger` (`uart_logger.sv`)**: Optional ASCII character logger for TX
    or RX serial traffic (`en_logger`, `use_rx_for_logger`,
    `write_logs_to_file`).

## Supported Baud Rates

`baud_rate_e` (`uart_agent_pkg.sv`) defines the following standard baud rates:

*   `BaudRate9600` (9,600 bps)
*   `BaudRate115200` (115,200 bps)
*   `BaudRate128Kbps` (128,000 bps)
*   `BaudRate230400` (230,400 bps)
*   `BaudRate256Kbps` (256,000 bps)
*   `BaudRate1Mbps` (1,000,000 bps)
*   `BaudRate1p5Mbps` (1,500,000 bps)

## Key Configuration Knobs (`uart_agent_cfg`)

*   `set_baud_rate(baud_rate_e b)`: Sets `baud_rate` and updates
    `vif.uart_clk_period`.
*   `set_parity(bit en_parity, bit odd_parity)`: Configures parity checking and
    generation.
*   `set_uart_period_glitch_pct(uint pct)`: Configures initial edge glitch
    duration on `uart_rx` (`< 20%`, recommended `0–10%`).
*   `set_max_drift_cycle_pct(uint pct)`: Configures allowed TX/RX bit-period
    drift tolerance (`< 50%`, default `25%`).
*   `en_tx_monitor`, `en_rx_monitor`, `en_tx_checks`, `en_rx_checks`,
    `re_enable_chk_mon_on_reset`: Enable/disable monitoring and protocol checks
    independently per direction.
*   `reset_asserted()` / `reset_deasserted(bit re_enable_chk_mon = 1)`:
    Propagate DUT reset state to the agent (since `uart_if` has no dedicated
    reset pin).

## Basic Usage

1.  Instantiate `uart_if` in the testbench top, connect `uart_rx` / `uart_tx` to
    the DUT, and publish the virtual interface via `uvm_config_db`:

    ```systemverilog
    uvm_config_db#(virtual uart_if)::set(null, "*.env.m_uart_agent*", "vif", uart_if);
    ```
2.  Create `uart_agent_cfg` and `uart_agent` in the environment, connect
    `monitor.tx_analysis_port` / `monitor.rx_analysis_port` to the scoreboard,
    and forward DUT reset transitions to `cfg.reset_asserted()` and
    `cfg.reset_deasserted()`.
3.  Configure `set_baud_rate()` and `set_parity()` before starting `uart_seq`
    items on `m_uart_agent.sequencer`.
