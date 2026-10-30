# High-Speed Device Remote Wakeup Test

**Testcase:** `caliptra_ss_usb_hs_dev_remote_wakeup`

## Overview

Verifies HS device suspend and resume signaling events, observed both on the
DUT UTMI `SuspendM` output and through `DEVCMDSTAT.DSUS_C`.

## Operation

The MCU firmware performs the two-phase hub bring-up required by the
hub-composite IP: `boot_usb_core_hub()` sets `HUB_CTRL.HUB_EN`, then
`usb_hub_connect()` sets `HUB_CONNECT`. Only after `HUB_CONNECT` does the hub
present itself on the bus, so the host sees connect / reset / HS chirp and the
VIP link reaches `ENABLED`. The firmware then clears `FORCE_NEEDCLK` with
`usb_allow_clock_stop()` so the UTMI clock can actually stop and `SuspendM` can
fall.

The VIP host runs SOF, stops it to drive suspend, waits for the DUT to enter
suspend, drives resume K-state with
`svt_usb_link_service_clear_suspend_sequence`, restarts SOF and waits for the
DUT to leave suspend. The firmware logs both `DSUS_C` events and halts.

## What Is Verified

- `DEVCMDSTAT.DSUS_C` set on suspend entry and on suspend exit (firmware
  reports `FAIL` if fewer than two events are seen)
- DUT UTMI `SuspendM` falls and rises in the observation window:
  `CHK_SUSPEND_SEEN` / `CHK_RESUME_SEEN` in
  `caliptra_ss_usb_suspend_resume_checker`, enabled by
  `+usb_suspend_resume_check=1`
- VIP upstream link reaches `ENABLED`, then `SUSPENDED`, then `ENABLED` again

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev_remote_wakeup_sequence.svh` | SVT VIP HS suspend/resume sequence; arms the DUT checker and closes its observation window |
| `caliptra_ss_usb_hs_dev_remote_wakeup_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_dev_remote_wakeup.c` | MCU firmware: hub bring-up and DSUS_C monitoring |
| `caliptra_ss_usb_hs_dev_remote_wakeup.mk` | Adds `+usb_suspend_resume_check=1` |
| `caliptra_ss_usb_hs_dev_remote_wakeup.yml` | Simulation run config |

## History

An earlier revision of the firmware omitted `usb_hub_connect()`, so the link
could never reach `ENABLED` and the test hung with zero UVM_ERROR. See
`docs/handover/claude_md/34_usb_hs_dev_remote_wakeup_hub_connect.md` in the
accessories repo.

# File contains AI-generated response based on internal company sources
