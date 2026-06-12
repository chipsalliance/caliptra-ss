# High-Speed DMA NBytes Residual Test

**Testcase:** `caliptra_ss_usb_hs_dev_nbyte`

## Overview

Verifies that the DMA NBytes residual field is zero after a 512-byte HS bulk OUT
transfer (exact byte count, no short packet).

## Operation

VIP host enumerates the HS device then sends 512 bytes of bulk OUT data to EP1.
MCU firmware checks the DMA endpoint NBytes residual field after the transfer
completes. Residual==0 means all bytes were received.

## What Is Verified

- HS bulk OUT transfer of exactly 512 bytes to EP1
- DMA NBytes residual field equals zero after transfer (no short packet)
- Correct DMA byte counting by the USB device controller

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev_nbyte_sequence.svh` | SVT VIP HS bulk OUT sequence (512 bytes) |
| `caliptra_ss_usb_hs_dev_nbyte_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_dev_nbyte.c` | MCU firmware checking DMA NBytes residual |
| `caliptra_ss_usb_hs_dev_nbyte.yml` | Simulation run config |
