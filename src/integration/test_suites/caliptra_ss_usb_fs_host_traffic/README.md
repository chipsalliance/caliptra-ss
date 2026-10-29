# Full-Speed Bulk Traffic Test

**Testcase:** `caliptra_ss_usb_fs_host_traffic`

## Overview

Verifies FS bulk OUT data transfer of 256 bytes with correct data pattern verification.

## Operation

VIP host enumerates the FS device (GET_DESCRIPTOR, SET_ADDRESS, SET_CONFIGURATION).
Host sends 256 bytes of incrementing bulk OUT data (words 0x100..0x13F) to EP1.
MCU firmware receives the data, verifies the pattern, and logs PASSED.

## What Is Verified

- Full FS enumeration sequence (control transfers)
- FS bulk OUT transfer of 256 bytes
- Data pattern correctness verified by MCU firmware (incrementing words 0x100..0x13F)

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_fs_host_traffic_sequence.svh` | SVT VIP enumeration + bulk OUT sequence |
| `caliptra_ss_usb_fs_host_traffic_test.svh` | UVM test class |
| `caliptra_ss_usb_fs_host_traffic.c` | MCU firmware receiving and verifying pattern |
| `caliptra_ss_usb_fs_host_traffic.yml` | Simulation run config |
