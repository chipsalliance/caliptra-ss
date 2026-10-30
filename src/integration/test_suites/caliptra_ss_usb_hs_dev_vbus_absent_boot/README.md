# caliptra_ss_usb_hs_dev_vbus_absent_boot

USB High-Speed **VBus-absent-at-boot** test: the SoC boots, enables its hub and
requests an upstream connect with **no host attached**, and only later does the
host appear.

## Why this test exists

Every other USB test in the suite has VBus already high before firmware touches
the USB core, so one ordering is never exercised:

| Time (measured, HS) | Event |
|---|---|
| 0 ns | VBus = 0 (VIP drives `VbusValid` = 0; the vbus driver forwards it) |
| **20 us** | VIP auto-attach, VBus -> 1 |
| ~32 us | firmware starts `boot_usb_core_hub()` |
| **55-70 us** | firmware sets `HUB_EN \| HUB_CONNECT` |

VBus arrives roughly 12 us *before firmware even begins USB bring-up*, so the
hub's upstream connect term

```vhdl
hub_connect <= sync_VBusDebounced and hub_dcon_q
-- ip_xxx_3511_hs_mem_compound_structure.a.vhdl:2103
```

is only ever evaluated with `VBusDebounced` already high. The
"firmware enables the hub while the cable is out" case is therefore completely
untested, even though it is the **normal self-powered-device case**: the SoC has
its own supply and boots whether or not a host is plugged in.

This test inverts the ordering.

## How the "no host" window is created

**No testbench change, no plusarg, no force.** VBus already starts at 0 in every
run. What hides the scenario is purely *timing*, so the test class moves the
VIP's own auto-attach:

```systemverilog
cfg.host_cfg.poweron_auto_attach_delay = VBUS_ATTACH_DELAY_PS;  // 150 us
cfg.dev_cfg.poweron_auto_attach_delay  = VBUS_ATTACH_DELAY_PS;
```

The VIP then performs the VBus rise itself at 150 us and
`caliptra_ss_usb_vbus_driver.sv` forwards it to `cptra_ss_usb_USB_VBus_i` as
usual. Both cfgs are deferred: `dev_cfg` is cloned into `remote_cfg` as the
device-side PHY model, and leaving it at 20 us would have the device PHY attach
while the host has not yet powered its port.

### Where 150 us comes from

Measured, not guessed. Across all **41 HS tests** of
`caliptra_nightly_regression_2026_10_24_05_31_55`, the timestamp of the firmware
log line `HUB_CTRL after HUB_CONNECT=1` was:

```
min 55.3 us   max 69.5 us   mean 59.9 us
```

The distribution is bimodal, not noisy:

| Cluster | Range | Members |
|---|---|---|
| A | 55.3-59.5 us | most of the HS suite (`hs_conn` 56.9, `hs_dev_bulk_out` 57.0, all `hs_dev1_*`, ...) |
| B | 69.2-69.5 us | the descriptor-override family (`hs_dev_get_*`, `hub_*descriptor`, `hub_qualifier`) |

150 us is ~2.2x the worst observed case, leaving an 80 us guard band above
cluster B. For reference the first bus reset in the normal flow lands at
233-247 us, so there is ample slack before anything times out.

## What is checked

### Firmware (`caliptra_ss_usb_hs_dev_vbus_absent_boot.c`)

| Phase | Check |
|---|---|
| 0a | `VBUS_DEBOUNCED == 0` **before** any USB bring-up. First test in the suite to ever observe this bit low. |
| 0b | `boot_usb_core_hub()` + `usb_hub_connect()` complete with VBus low. |
| 0c | `VBUS_DEBOUNCED` still 0 **after** `HUB_CONNECT` - firmware's request alone cannot connect the hub. |
| 1 | `VBUS_DEBOUNCED` makes a genuine 0 -> 1 transition (bounded by `USB_VBUS_WAIT_TIMEOUT`). |
| 2 | 7 EP0 control transfers serviced, **and** a bus reset observed (`usb_bus_reset_count` must advance). |
| 2b | `DEVCMDSTAT.SPEED == HS (2)`. |

### Sequence (`caliptra_ss_usb_hs_dev_vbus_absent_boot_sequence.svh`)

1. Starts **no SOF** and does nothing - firmware is booting into a dead bus.
2. **Negative window (130 us):** asserts the VIP link never reaches `ENABLED`.
   Implemented as a timer-vs-watcher race, not an end-of-window sample, so a
   transient spurious attach cannot slip through. This is the host-side half of
   the Phase 0c assertion.
3. Waits for the link to leave `POWERED_OFF` (evidence the attach happened),
   then starts SOF.
4. `wait_for_link_enabled()`, 50 us settle for the firmware's `DRES_C` ->
   `usb_ep0_reinit()` path, then `enumerate_hub_and_usbdc0()`.

### Pass criterion

The conjunction of: the negative window, the full hub-aware enumeration
completing (which only succeeds if firmware is servicing real SETUP tokens
forwarded through the hub), and the firmware's `SPEED == HS` assertion.

Firmware `FAIL` lines become UVM_ERRORs via
`caliptra_ss_mcu_console_fail_checker` (`+mcu_console_fail_check=1` is global in
`tools/scripts/Makefile`).

## Notable design facts recorded by this test

- **HS, not FS, on purpose.** The FS boot path sets `DEVCMDSTAT.FORCE_VBUS`,
  which makes `VBUS_DEBOUNCED` read 1 regardless of the pin and would mask the
  entire scenario. HS leaves `FORCE_VBUS` clear.
- **`boot_usb_core_hub()` is already VBus-agnostic.** `usb.c` gates its blocking
  `usb_wait_vbus_debounced()` on `if (!hub_en && !fs_en)`; the hub path skips it
  because the hub, not the device controller, owns the upstream connect. This
  test is what proves that.
- **`hub_write_lock` has no VBus term.** It is driven by `HUB_EN & HUB_CONNECT`,
  so the descriptor flip-flop array freezes even though the hub never appeared
  on the bus. Logged in Phase 0c.
- **Why no EP1 traffic.** The firmware is an EP0-only event loop; unlike the
  `bulk_loopback` firmware it has no EP1 OUT -> IN copy handler, so a bulk
  transfer would never be answered. Endpoint traffic after a late attach belongs
  in a follow-up test paired with loopback-capable firmware.

## Run

```bash
cd $CALIPTRA_SS_ROOT
python3 tools/run_caliptra_test.py caliptra_ss_usb_hs_dev_vbus_absent_boot
```

## Possible follow-ups

- FS variant - needs a way to keep `FORCE_VBUS` clear, or it is vacuous.
- `dev1` variant (USBDC1 behind hub port 2).
- Late attach followed by EP1 traffic, with loopback-capable firmware.
- Host bus reset landing *between* `HUB_EN` and `HUB_CONNECT`, while the
  descriptor array is still unlocked.

<!-- File contains AI-generated response based on internal company sources -->
