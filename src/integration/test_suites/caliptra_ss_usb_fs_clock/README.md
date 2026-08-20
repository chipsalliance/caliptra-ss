# Full-Speed (FS) Clock/Link Test

**Testcase:** `caliptra_ss_usb_fs_clock`

## Overview

Verifies that the USB device controller links up correctly at Full-Speed (FS, 12 Mbit/s).

## Operation

Configures the SVT VIP host with high_speed_capable=0 to force FS mode.
MCU firmware boots USB in FS mode. Host waits for FS link ENABLED and runs SOF.

## What Is Verified

- USB FS link comes up at 12 Mbit/s
- SOF packets generated at FS rate
- Device controller operates correctly at FS clock speed

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_fs_clock_sequence.svh` | SVT VIP host sequence (FS mode) |
| `caliptra_ss_usb_fs_clock_test.svh` | UVM test class |
| `caliptra_ss_usb_fs_clock.c` | MCU firmware for FS link bring-up |
| `caliptra_ss_usb_fs_clock.yml` | Simulation run config |
