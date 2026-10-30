# USB HS Hub-Bypass Enumeration

**Testcase:** `caliptra_ss_usb_hs_dev_hub_bypass_enum`
**UVM test:** `caliptra_ss_usb_hs_dev_hub_bypass_enum_test`
**Category / regression:** Directed, Nightly, L1, `caliptra_ss_top_tb`

Enumerates USBDC0 (device0) with the on-chip hub **disabled**, so device0 is
connected directly to the upstream USB link. This is the only enumerating test
in the suite that runs with `HUB_CTRL.HUB_EN = 0`.

---

## 1. Why this test exists

`hub_enable` is not a strap. `USB_EnableHub` is tied `1'b0` at top level
(`caliptra_ss_top.sv`), so `hub_enable_q` inside the compound IP follows the
firmware-written `HUB_CTRL.HUB_EN` bit (`ep0_mem(C_HUB_CS)(0)` in
`usb_ep0_hub_descr.m.vhdl`). Leaving that bit clear is what selects the
hub-bypass topology, and it flips **four** muxes in
`ip_xxx_3511_hs_mem_compound_structure.a.vhdl` to their else-leg at once:

```vhdl
usb_dev_connect         <= hub_connect when hub_enable_q = '1'
                           else dev0_usbreg_dev_connect;
usbreg_deviceenabled(0) <= hub_connect when hub_enable_q = '1' else '0';
usbreg_deviceenabled(1) <= hub_port_enable(0) and dev0_usbreg_deviceenabled
                           when hub_enable_q = '1'
                           else dev0_usbreg_deviceenabled;
upd_dev0_portreset      <= dev0_portreset when hub_enable_q = '1'
                           else sync_busreset;
```

| With `HUB_EN = 0` | Consequence |
|---|---|
| `usb_dev_connect` | device0's own `DCON` reaches the upstream port; the hub cannot connect |
| `usbreg_deviceenabled(0)` | the hub is forced not-enabled, i.e. not a bus participant at all |
| `usbreg_deviceenabled(1)` | device0's enable passes through ungated by any hub port enable |
| `upd_dev0_portreset` | device0's port reset is the upstream bus reset directly |

Every other enumerating USB test sets `HUB_EN`, so all four else-legs were
previously uncovered. The `hub_enable_q = '1'` behaviour is thoroughly covered
by the rest of the suite; this test is the counterpart.

---

## 2. Address map (differs from every other test)

| Topology | hub | USBDC0 |
|---|---|---|
| hub mode (all other tests) | address 1 | address 2 |
| **bypass (this test)** | never addressed | **address 1** |

In bypass topology there is exactly one device on the bus, so it takes the
first address the host hands out. This is not a typo in the sequence or the
firmware - both carry a named constant and a comment saying so.

---

## 3. Firmware

`caliptra_ss_usb_hs_dev_hub_bypass_enum.c`. The bypass path is already
implemented in the shared library, so the firmware is small. The entire
topology selection is the `hub_en` argument of `boot_usb_core(fs_en, hub_en)`:

```c
if (hub_en) { usb_hub_init_and_connect(); }        // writes HUB_EN
if (!hub_en && !fs_en) { usb_wait_vbus_debounced(); }
if (hub_en) { reg_data |= FORCE_NEEDCLK; }
```

`mcu_cptra_init_d()` forwards `args.usb_hub_en` to it, so the test requests:

```c
mcu_cptra_init_d(..., .cfg_boot_usb_core=true,
                      .usb_hub_en=false,
                      .usb_fs_en=false);
```

`usb_hub_en` is already `false` by default in `caliptra_ss_lib.h`, but it is
passed explicitly so the intent is visible at the call site and cannot be
changed out from under the test by an edit to that default. `usb_hub_connect()`
is **never** called - there is no hub to connect, and calling it would set
`HUB_EN` and silently turn this into an ordinary hub-mode test.

### Firmware checks

| Phase | Check |
|---|---|
| 0 | `HUB_CTRL` reads back with `HUB_EN = 0` and `HUB_CONNECT = 0`. Direct assertion that the topology under test is actually in force. |
| 1 | `DEVCMDSTAT` has `DEV_EN` and `DCON` set, and `FORCE_NEEDCLK` **clear** (that bit is only set by the hub-mode boot path, so a set bit is independent evidence the hub path ran). |
| 2 | All 7 enumeration control transfers were handled. |
| 3 | At least one bus reset (`DRES_C`) was serviced - the most direct firmware-visible evidence that the reparented `upd_dev0_portreset` leg delivers the host reset. |
| 4 | `DEVCMDSTAT.DEV_ADDR == 1` and `SPEED == HS` (2). |

Verdict follows the `total_errors` pattern: any failure sends
`SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL)`, which is the only thing that actually
fails a run (a `VPRINTF` saying "FAIL" does not - see
`claude_md/16_usb_silent_fail_verdict_gap.md`). `TB_CMD_TEST_PASS` is
deliberately never sent: it `$finish`es before the UVM `final_phase` and would
discard the host-side sequence checks.

---

## 4. Host sequence

`caliptra_ss_usb_hs_dev_hub_bypass_enum_sequence` extends
`caliptra_ss_usb_base_sequence` and uses only its existing API. It calls **no**
hub helper - `hub_enum_stepA` / `hub_port_bringup_stepB` /
`usbdc0_enum_stepC` are all wrong here, because there is no hub to address at
address 1, no downstream port to power or reset, and USBDC0 answers the default
address 0 from the start. The flat 7-transfer enumeration is written inline, so
nothing shared needed modifying for this test.

1. Start SOF, wait for the link to reach `ENABLED` (bounded). The link can only
   come up through the `hub_enable_q = '0'` leg of `usb_dev_connect`, so this
   wait is already the first functional check.
2. `#20us` settle so the firmware can service `DRES_C` and re-prime EP0.
3. `GET_DESCRIPTOR(DEVICE, 18)` @0, checked as **`dev0`**. If the hub had
   answered the bytes would be its class-0x09 descriptor and this check fails -
   this is the discriminator for the whole test.
4. `GET_STATUS(DEVICE)` @0, expect **`0x0001`**, not `0x0000`. The shared
   `usb.c` EP0 handler hardcodes bit[0] Self-Powered to 1, so `0x0001` (and
   `0x0003` after a SET_FEATURE(REMOTE_WAKEUP), which this test never issues)
   are the only values it can return. Do not derive this from the USB spec -
   read the handler. The pre-existing `caliptra_ss_usb_hs_dev_get_status` test
   asserts the same values.
5. `SET_ADDRESS(1)` @0, `#5us`, then the mandatory VIP anchor update.
6. `GET_DESCRIPTOR(DEVICE, 18)` @1 plus the RTL committed-address check on
   `dev0`.
7. `GET_CONFIGURATION` @1 (still 0), `SET_CONFIGURATION(1)`,
   `GET_CONFIGURATION` verify.
8. `check_device_speed("dev0", 2'b10)` - the chirp runs off the reparented
   reset net here, and `usb_pie`'s init path asserts `set_dev_fs`, so a missed
   chirp would leave the link at FS with enumeration still succeeding.
9. **Negative assertion:** `check_device_address(..., "hub", 0)`. The hub's
   committed address must still be 0. In hub mode step A drives it to 1.
   This is what makes the positive result specific to the bypass path rather
   than merely "some device enumerated".

---

## 5. Why HS and not FS

Full-Speed bring-up sets `DEVCMDSTAT.FORCE_VBUS` and, via
`usb_hub_force_fullspeed()`, `HUB_CTRL.FORCE_FULLSPEED`. Writing `HUB_CTRL` at
all in a test whose premise is "`HUB_CTRL.HUB_EN` stays 0" muddies the
scenario, and `FORCE_VBUS` would additionally mask the `VBUS_DEBOUNCED`
observation in Phase 1. HS touches neither, so the HS variant is the clean one.
An FS sibling would need `FORCE_FULLSPEED` set without disturbing `HUB_EN`,
which is a separate piece of work.

---

## 6. Note on the blocking VBus wait

The bypass leg is the **one** path in `boot_usb_core()` that calls the unbounded
`usb_wait_vbus_debounced()` before asserting `DCON`, and it is right to: with
the hub out of the picture nothing else gates the upstream connect, so the
device must not pull up before VBus debounces. It cannot hang here because the
VIP auto-attaches at 20 us (`poweron_auto_attach_delay` in
`caliptra_ss_usb_shared_cfg.svh`) and the MCU only reaches USB bring-up at
~32 us, so VBus is already high on arrival. Phase 1 logs the observed
`VBUS_DEBOUNCED` value so a future change to the attach timing shows up as a
log line instead of a silent hang.

The deliberately-late-VBus scenario is a different test,
`caliptra_ss_usb_hs_dev_vbus_absent_boot`, and it is hub mode precisely because
hub mode skips this wait.

---

## 7. Files

| File | Purpose |
|---|---|
| `caliptra_ss_usb_hs_dev_hub_bypass_enum.c` | MCU firmware: bypass boot + 5 phases of checks |
| `caliptra_ss_usb_hs_dev_hub_bypass_enum.yml` | Run config, `CALIPTRA_SS_CLK_FREQ=400`, no `BUILD_CFLAGS` |
| `cptra_bringup.c` | symlink to `../libs/usb/bringup/cptra_bringup.c` |
| `README.md` | this file |
| `uvm/usb/..._sequence.svh` | flat 7-transfer enumeration + the hub-never-addressed check |
| `uvm/usb/..._test.svh` | HS test class, no VIP conversion needed |
| `uvm/usb/caliptra_ss_usb_test_pkg.sv` | 2 includes |
| `stimulus/testsuites/caliptra_ss_master_test_list.csv` | Directed / Nightly / L1 row |
| `nxp_dv_accessories/.../USB_caliptra_ss_top_tb_regression.yml` | registration (what `run_caliptra_test.py -list` reads) |

Note: `run_caliptra_test.py -list` enumerates the **regression yml**, not the
`test_suites/` directory, so a new test is invisible to the runner until it is
added there.

---

## 8. How to run

```bash
python3 tools/run_caliptra_test.py -t caliptra_ss_usb_hs_dev_hub_bypass_enum
```

Expected: `MCU: USB HS hub-bypass enumeration test PASSED` in
`mcu_console.log`, no `UVM_ERROR`, and the sequence's closing
`Hub-bypass enumeration of USBDC0 complete` line.

## 9. Measured results

First simulated run (after the GET_STATUS expectation fix in section 4):

| Time | Observation |
|---|---|
| 40195 ns | `boot_usb_core - initializing USB device controller (hub_en=0 fs_en=0)` |
| 62155 ns | Phase 0: `HUB_CTRL=0x10400800` - `HUB_EN` (bits 0 and 7) and `HUB_CONNECT` (bit 16) all clear |
| 65522 ns | Phase 1: `DEVCMDSTAT=0x10410880` - `DEV_EN`+`DCON` set, `FORCE_NEEDCLK` clear |
| 355620 ns | Phase 2: all 7 enumeration control transfers handled |
| 357625 ns | Phase 3: 1 bus reset observed via the bypass reset path |
| 359812 ns | Phase 4: device0 committed address 1 |
| 361335 ns | Phase 4: link negotiated HS (SPEED=2) |

Those two register values are the direct evidence for the topology: the hub was
never enabled and device0 drove the upstream connect on its own.

<!-- File contains AI-generated response based on internal company sources -->
