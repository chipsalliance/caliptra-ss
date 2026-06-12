# Full-Speed Root Endpoint Bulk OUT Test

**Testcase:** `caliptra_ss_usb_fs_root2`

## Overview

Verifies FS bulk OUT transfer to EP1 with 64 bytes (FS max packet size).

## Operation

VIP host enumerates the FS device. MCU firmware arms EP1 OUT with a 64-byte buffer.
VIP host sends 64 bytes of bulk OUT data to EP1. MCU firmware detects the EP1 OUT
interrupt and logs PASSED.

## What Is Verified

- EP1 OUT armed correctly by MCU firmware
- VIP host bulk OUT transfer delivers 64 bytes to EP1
- EP1 OUT interrupt fires and is handled by MCU firmware

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_fs_root2_sequence.svh` | SVT VIP bulk OUT sequence |
| `caliptra_ss_usb_fs_root2_test.svh` | UVM test class |
| `caliptra_ss_usb_fs_root2.c` | MCU firmware arming EP1 OUT and handling interrupt |
| `caliptra_ss_usb_fs_root2.yml` | Simulation run config |
