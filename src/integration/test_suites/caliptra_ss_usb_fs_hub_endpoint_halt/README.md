# USB Hub ENDPOINT_HALT Test (Full-Speed)

**Testcase:** `caliptra_ss_usb_fs_hub_endpoint_halt`

## Overview

Boots the MCU, brings up the USB hub-composite IP (HUB RAM programming,
HUB_EN, then HUB_CONNECT) and Caliptra core, enumerates the **hub alone** (no
downstream port power-up, no USBDC0 enumeration), then exercises the complete
USB 2.0 endpoint-feature round trip on the hub interrupt IN endpoint:
`GET_STATUS` baseline, `SET_FEATURE(ENDPOINT_HALT)`, `GET_STATUS`,
`CLEAR_FEATURE(ENDPOINT_HALT)`, `GET_STATUS`. The scenario is control-transfer
only: every step runs on EP0 and no data traffic is driven to the halted
endpoint.

The requests are decoded entirely in hub EP0 hardware (SETUP-match ROM plus
`usb_ep0_handler`), so the MCU firmware only provides bring-up and the standard
EP0 poll loop.

## Full-Speed Deltas

Port of `caliptra_ss_usb_hs_hub_endpoint_halt`. Only the speed plumbing
changes; the request encodings, the `wIndex` and the expected status words are
identical because the decode path under test (`usb_ep0_handler` plus
`usb_ep_config_handler`) is speed independent. Running the round trip at full
speed proves the SETUP mask compare and the `reg_ep_stall` set/clear path do
not depend on HS timing or on the HS electrical gate.

| Item | HS | FS |
|------|----|----|
| `high_speed_capable` | 1 (chirp performed) | 0 (no chirp) |
| Host/device/endpoint speed | `HS` | `FS`, both default endpoints re-stamped |
| Max packet size | HS defaults | `SVT_USB_FS_CONTROL_MAX_PACKET_SIZE` / `SVT_USB_FS_BULK_MAX_PACKET_SIZE` |
| `tddis` / `tend_to_end_delay_fs` | HS defaults | 2 ms |
| `tinactivity` | HS default | 5 ms |
| `drive_reset_time` | HS default | 150 us |
| Sequence `SETTLE_DELAY` | 20 us | 160 us (FS frame period is 1 ms) |
| Firmware bring-up | `boot_usb_core_hub()` | `boot_usb_core_fs()` (sets `DEVCMDSTAT.PFSC`) |
| `USB_POLL_TIMEOUT` | 5000 | 10000 |

Both default endpoint configurations must be re-stamped to FS even though
`endpoint_cfg[1]` carries no traffic here: leaving it at the HS max packet size
makes `cfg.is_valid()` fail during the build phase.

The FS link-collapse hazard documented for `caliptra_ss_usb_fs_hub_test_mode`
does not apply: this scenario never issues `SET_FEATURE(TEST_MODE)`, all
traffic stays on EP0 and the link stays up for the whole run.

## Request Encoding

| Field | SET_FEATURE | CLEAR_FEATURE | GET_STATUS |
|-------|-------------|---------------|------------|
| `bmRequestType` | `0x02` | `0x02` | `0x82` |
| `bRequest` | `0x03` | `0x01` | `0x00` |
| `wValue` | `0x0000` (ENDPOINT_HALT) | `0x0000` | `0x0000` |
| `wIndex` | `0x0081` | `0x0081` | `0x0081` |
| `wLength` | `0` | `0` | `2` |

`wIndex = 0x0081` means direction IN, endpoint number 1.

## Why Endpoint 1 IN

`usb_ep_config_hub_pkg.p.vhdl` declares `C_NBPHYSEP = 2` and gives device 0
(the hub) exactly one non-control endpoint: `EPNB = 1`, `EPDIR = EP_IN`,
`NON_ISO`. Endpoint 1 IN is therefore the only Halt-able endpoint on the hub.

`func_epconfig_link` maps an IN endpoint to offset `4*EPNB+2` and an OUT
endpoint to offset `4*EPNB`, with the link array zero-filled. Endpoint 1 IN
maps to offset 6 -> physical endpoint bit 0, and offset 0 (`wIndex = 0x0000`,
EP0 OUT) also reads physical bit 0 because of that zero fill. The two indices
alias, so the test uses `0x0081` exclusively: halting EP0 would kill the
control pipe the test depends on.

`usb_ep0_hub_descr.m.vhdl` admits all three endpoint requests for device 0 with
`wIndex` mask `0xFF7E` against match `0x0000` - bits 0 and 7 are don't-care and
every other bit must be zero, so `0x0081` is admitted. The `wValue` mask is
`0xFFFF` against match `0x0000`, so only feature selector ENDPOINT_HALT is
ever accepted.

## Operation

The VIP host sequence `caliptra_ss_usb_fs_hub_endpoint_halt_sequence`:

1. Waits for the host link to reach ENABLED and starts SOF generation.
2. Enumerates the hub only (`hub_enum_stepA`), leaving it at device address 1
   with the VIP anchor already on that address.
3. `GET_STATUS(ENDPOINT, 0x0081)` must return `0x0000` - `reg_ep_stall` resets
   to 0.
4. `SET_FEATURE(ENDPOINT, ENDPOINT_HALT, 0x0081)`.
5. `GET_STATUS(ENDPOINT, 0x0081)` must return `0x0001`.
6. `CLEAR_FEATURE(ENDPOINT, ENDPOINT_HALT, 0x0081)`.
7. `GET_STATUS(ENDPOINT, 0x0081)` must return `0x0000` again.

## Observability

The Halt flop is `usb_ep_config_handler.reg_ep_stall`, a VHDL internal signal
with no testbench probe. `usb_ep0_handler` drives `ep_set_stall` /
`ep_clear_stall` into that module and reads the state back through
`epconfig_stall`, returning it as bit 0 of the `GET_STATUS` data stage. The
`check_get_status()` comparisons are therefore a genuine cross-module read of
the real flop, not a shadow register. `CLEAR_FEATURE` additionally asserts
`reg_ep_toggle_reset`, as USB 2.0 requires for a cleared Halt.

A packet-level proof that the halted endpoint also STALLs an IN token is
deliberately not attempted. The hub interrupt IN endpoint is declared with no
buffer, so an IN probe does not terminate cleanly: a halted IN transfer is
retried by the VIP until its transfer-level timeout, which only lengthens the
run without adding register coverage.

## What Is Verified

- USB hub-composite bring-up and hub-only enumeration at Full Speed
- `GET_STATUS(ENDPOINT)` reset value on the hub interrupt IN endpoint
- `SET_FEATURE(ENDPOINT, ENDPOINT_HALT)` sets the Halt status bit
- `CLEAR_FEATURE(ENDPOINT, ENDPOINT_HALT)` clears the Halt status bit again
- EP0 keeps answering control transfers throughout the halt window

## Known RTL Gaps

`usb_ep0_handler.m.vhdl` carries three identical designer TODOs at the
SET_FEATURE, GET_STATUS and CLEAR_FEATURE endpoint branches: "how to generate a
stall on an endpoint that is disabled and which cannot be masked by SETUP_MASK
bits". A request naming a non-existent endpoint is therefore not rejected; it
silently aliases onto a physical endpoint bit. This test deliberately stays on
the one legal index.

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_fs_hub_endpoint_halt_sequence.svh` | Hub-only enumeration + ENDPOINT_HALT control-transfer round trip |
| `caliptra_ss_usb_fs_hub_endpoint_halt_test.svh` | FS UVM test class (FS VIP conversion + selects the sequence as default_sequence) |
| `caliptra_ss_usb_fs_hub_endpoint_halt.c` | MCU firmware: hub bring-up + EP0 event loop |
| `caliptra_ss_usb_fs_hub_endpoint_halt.yml` | Simulation run config |
