# USB Hub SET_FEATURE(TEST_MODE) Test (Full-Speed)

**Testcase:** `caliptra_ss_usb_fs_hub_test_mode`

## Overview

Full-Speed counterpart of `caliptra_ss_usb_hs_hub_test_mode`. Boots the MCU,
brings up the USB hub-composite IP (HUB RAM programming, HUB_EN, then
HUB_CONNECT) and Caliptra core, enumerates the **hub alone** (no downstream
port power-up, no USBDC0 enumeration), then exercises the USB 2.0
`SET_FEATURE(DEVICE, TEST_MODE)` request on the hub with one invalid and one
valid test selector. The link attaches at FS (12 Mbit/s): the VIP is converted
to Full Speed and the firmware suppresses the device K-chirp.

Why an FS variant is meaningful: the request is decoded entirely in hub EP0
hardware (SETUP-match ROM plus `usb_ep0_handler`), and that decode path is
speed-independent. Running it at FS proves the accept/reject logic and the
`usb_phy_test_mode` load are not tied to the HS attach path. It does **not**
claim to verify the PHY-level FS electrical test modes - at FS the PIE drive
table for the test modes is an HS construct (see
`docs/handover/claude_md/20_usb_phy_test_mode_rtl_and_vip.md` in the DV
accessories repo).

Request encoding (USB 2.0 section 9.4.9):

| Field | Value |
|-------|-------|
| `bmRequestType` | `0x00` (host-to-device, standard, recipient = device) |
| `bRequest` | `0x03` (SET_FEATURE) |
| `wValue` | `0x0002` (TEST_MODE feature selector) |
| `wIndex[15:8]` | test selector |
| `wLength` | `0` |

Valid test selectors are 1 (Test_J), 2 (Test_K), 3 (Test_SE0_NAK),
4 (Test_Packet) and 5 (Test_Force_Enable). Anything above 5 must be rejected.

## Operation

The VIP host sequence `caliptra_ss_usb_fs_hub_test_mode_sequence`:

1. Waits for the host link to reach ENABLED and starts SOF generation, then
   settles `#160us` (8x the HS `#20us`, matching the 1 ms FS frame period).
2. Enumerates the hub only (`hub_enum_stepA`), leaving it at device address 1
   with the VIP anchor already on that address.
3. Draws a random **invalid** selector from 6..255 and issues
   `SET_FEATURE(DEVICE, TEST_MODE)` with it. The hub EP0 handler stalls the
   request, so `check_phy_test_mode("hub", 3'b000)` must still see the reset
   value.
4. Issues a hub-class `GET_HUB_STATUS` to prove the stalled request did not
   disturb the link.
5. Draws a random **valid** selector from 1..5, issues the same request and
   checks `check_phy_test_mode("hub", selector[2:0])`.

Both draws are printed at `UVM_LOW` so a failing seed is reproducible.

Accept/reject is not visible in the VIP transfer item, so it is read from the
RTL: `usb_ep0_handler_1.usb_phy_test_mode` is mirrored by `usb_dev_addr_probe`
as `hub_phy_test_mode` and compared through the data-check API. The register
resets to `3'b000`, is loaded with `selector[2:0]` only when the handler
accepts, and has no clear path.

**The accepted request is the last USB activity of the test by design.** Once
`usb_phy_test_mode` is non-zero the PIE enters `BUS_EVENT_TEST_MODE`, whose
only documented exit is a power cycle (`usb_pie.m.vhdl`). At Full Speed this
state additionally forces the HS electrical gate (`xcvrselect = 0` /
`termselect = 0`, whereas FS idle needs `1` / `1`), so the FS link itself drops.
That is harmless here only because the final check reads an RTL probe and not
the bus: never append a transfer after the accepted SET_FEATURE. For the same
reason no `CLEAR_FEATURE(TEST_MODE)` is attempted (the hub EP0 SETUP-match ROM
mask excludes feature selector 2 and the handler has no clear path - see
`docs/usb/usb_hub_test_mode_rtl_gaps_report.md` in the DV accessories repo).

The test is registered in the master test list with the **Random** category so
nightly multi-seed runs sweep the selector space.

## Full-speed deltas against the HS test

| Item | HS | FS |
|------|----|----|
| VIP config | default (HS) | `high_speed_capable=0`, host/dev `speed=FS`, `connected_bus_speed=FS`, `functionality_support=FS`, both default endpoints (EP0 control, EP1 bulk) re-stamped to FS speed + FS max packet size (required or `cfg.is_valid()` fails in `build_phase`) |
| Sequence settle delay | `20us` | `160us` |
| Firmware bring-up | `boot_usb_core_hub()` | `boot_usb_core_fs()` (sets `DEVCMDSTAT.PFSC`, bit 21, to suppress the device K-chirp) |
| Firmware `USB_POLL_TIMEOUT` | 5000 | 20000 |

## What Is Verified

- USB hub-composite bring-up and hub-only enumeration at Full Speed
- `SET_FEATURE(DEVICE, TEST_MODE)` rejection for test selectors above 5
- `SET_FEATURE(DEVICE, TEST_MODE)` acceptance for test selectors 1..5, with the
  correct selector value latched into `usb_phy_test_mode`, independent of the
  attached link speed
- EP0 survives a stalled control transfer (GET_HUB_STATUS still answers)

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_fs_hub_test_mode_sequence.svh` | Hub-only enumeration + invalid/valid SET_FEATURE(TEST_MODE) VIP sequence, FS-retimed |
| `caliptra_ss_usb_fs_hub_test_mode_test.svh` | FS UVM test class (FS VIP conversion block + selects the sequence as default_sequence) |
| `caliptra_ss_usb_fs_hub_test_mode.c` | MCU firmware: FS hub bring-up + EP0 event loop |
| `caliptra_ss_usb_fs_hub_test_mode.yml` | Simulation run config |
| `usb_dev_addr_probe.sv` | SV probe mirroring `usb_phy_test_mode` out of the VHDL hub |
