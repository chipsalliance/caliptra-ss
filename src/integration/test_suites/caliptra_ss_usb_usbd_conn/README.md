# USB Device Connection Detection Test

**Testcase:** `caliptra_ss_usb_usbd_conn`

## Overview

Verifies basic USB device connection detection via DEVCMDSTAT.DCON.

## Operation

MCU firmware polls DEVCMDSTAT.DCON after boot. VIP host connects (HS chirp, link-up).
Firmware detects DCON=1 and logs PASSED.

## What Is Verified

- DEVCMDSTAT.DCON asserted when VIP host connects
- MCU firmware correctly polls and reads DCON bit
- HS chirp and link-up sequence completes

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_usbd_conn_sequence.svh` | SVT VIP HS connect sequence |
| `caliptra_ss_usb_usbd_conn_test.svh` | UVM test class |
| `caliptra_ss_usb_usbd_conn.c` | MCU firmware polling DEVCMDSTAT.DCON |
| `caliptra_ss_usb_usbd_conn.yml` | Simulation run config |
