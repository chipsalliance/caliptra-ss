# High-Speed Host Bulk OUT Test

**Testcase:** `caliptra_ss_usb_hs_host_bulk_out`

## Overview

Verifies HS bulk OUT host-to-device transfer with full EP0 enumeration handling.

## Operation

VIP host enumerates the HS device and sends bulk OUT data to EP1.
MCU firmware boots the HS device and handles EP0 control transfers throughout the test.

Note: This test was originally a host-mode DUT test. In the Caliptra environment
the DUT is always a USB device; the SVT VIP acts as host.

## What Is Verified

- Full HS EP0 enumeration (control transfers handled by MCU firmware)
- HS bulk OUT transfer delivered from VIP host to device EP1
- MCU firmware correctly processes EP0 throughout the transfer

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_host_bulk_out_sequence.svh` | SVT VIP HS enumeration + bulk OUT sequence |
| `caliptra_ss_usb_hs_host_bulk_out_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_host_bulk_out.c` | MCU firmware HS device + EP0 handler |
| `caliptra_ss_usb_hs_host_bulk_out.yml` | Simulation run config |
