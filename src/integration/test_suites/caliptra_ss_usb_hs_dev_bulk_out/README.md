# High-Speed Bulk OUT Transfer Test

**Testcase:** `caliptra_ss_usb_hs_dev_bulk_out`

## Overview

Verifies HS bulk OUT transfer of 4096 bytes with full data integrity check.

## Operation

VIP host enumerates the HS device, then sends 4096 bytes of bulk OUT data to EP1
(pattern: word[i] = i). MCU firmware receives data, verifies each 32-bit word matches
the pattern, and logs PASSED.

## What Is Verified

- HS bulk OUT transfer of 4096 bytes to EP1
- Data integrity: each 32-bit word verified against incrementing pattern (word[i] == i)
- MCU firmware DMA reception and pattern checking

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev_bulk_out_sequence.svh` | SVT VIP HS bulk OUT sequence |
| `caliptra_ss_usb_hs_dev_bulk_out_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_dev_bulk_out.c` | MCU firmware data verification |
| `caliptra_ss_usb_hs_dev_bulk_out.yml` | Simulation run config |
