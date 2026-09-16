# Full-Speed Bulk Loopback Test

**Testcase:** `caliptra_ss_usb_fs_dev_bulk_loopback`

## Overview

Verifies FS bulk data transfer integrity with a 64-byte OUT-to-IN loopback on EP1.

## Operation

VIP host enumerates the FS device, then sends 64 bytes of bulk OUT data to EP1.
MCU firmware detects the EP1 OUT interrupt, copies the received data to the EP1 IN
buffer, and arms EP1 IN. VIP host reads back 64 bytes from EP1 IN.

## What Is Verified

- FS bulk OUT transfer to EP1 (64 bytes, FS max packet size)
- MCU firmware loopback copy from EP1 OUT to EP1 IN buffer
- FS bulk IN transfer from EP1 (64 bytes read back by VIP host)
- End-to-end data integrity of 64 bytes

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_fs_dev_bulk_loopback_sequence.svh` | SVT VIP bulk OUT+IN sequence |
| `caliptra_ss_usb_fs_dev_bulk_loopback_test.svh` | UVM test class |
| `caliptra_ss_usb_fs_dev_bulk_loopback.c` | MCU firmware loopback handler |
| `caliptra_ss_usb_fs_dev_bulk_loopback.yml` | Simulation run config |
