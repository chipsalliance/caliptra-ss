# High-Speed Device Connection Test

**Testcase:** `caliptra_ss_usb_hs_conn`

## Overview

Verifies HS USB device connection at 480 Mbit/s and DEVCMDSTAT.DCON assertion.

## Operation

VIP host performs HS chirp (high_speed_capable=1). MCU firmware polls
DEVCMDSTAT.DCON. Firmware detects HS connection and logs PASSED.

## What Is Verified

- HS chirp sequence completes at 480 Mbit/s
- DEVCMDSTAT.DCON set correctly after HS link-up
- MCU firmware detects HS connection

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_conn_sequence.svh` | SVT VIP HS connect sequence |
| `caliptra_ss_usb_hs_conn_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_conn.c` | MCU firmware polling DEVCMDSTAT.DCON |
| `caliptra_ss_usb_hs_conn.yml` | Simulation run config |
