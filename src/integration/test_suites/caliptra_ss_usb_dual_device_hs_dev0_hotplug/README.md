# caliptra_ss_usb_dual_device_hs_dev0_hotplug

Downstream-port hotplug **isolation** test for the USB 2.0 compound device
(embedded virtual hub + two software device controllers), running at
**High Speed**.

## Intent

While **DEV1 (USBDC1, hub port 2)** keeps performing EP1 bulk loopback
transfers, **DEV0 (USBDC0, hub port 1)** is repeatedly disconnected and
reconnected. The test proves that DEV0's hotplug activity does **not**
perturb DEV1: DEV1 never sees a bus/port reset, never loses its assigned
device address, and its data transfers keep completing correctly across every
DEV0 connect/disconnect cycle.

## Mechanism: why toggling DEV0 `DCON` is a port-1-only event

From `third_party/usb2/.../ip_xxx_3511_hs_mem_compound_structure.a.vhdl`:

```vhdl
hub_port_connect(0) <= dev0_usbreg_dev_connect;   -- DEV0 DCON == hub port 1 connect
hub_port_connect(1) <= dev1_usbreg_dev_connect;   -- DEV1 DCON == hub port 2 connect

usb_dev_connect <= hub_connect when hub_enable_q = '1' else dev0_usbreg_dev_connect;
hub_connect     <= sync_VBusDebounced and hub_dcon_q;

dev0_portreset  <= '1' when hub_port_reset(0) = '1' or sync_busreset = '1' else '0';
dev1_portreset  <= '1' when hub_port_reset(1) = '1' or sync_busreset = '1' else '0';
```

Key points:

* Each device controller's `DEVCMDSTAT.DCON` bit drives the *connect* status of
  its own downstream hub port only.
* Once `HUB_EN = 1`, the **upstream** connect (`usb_dev_connect`) is owned by
  the hub's own `HUB_CONNECT` bit, **not** by DEV0's `DCON`. So writing
  `USBDC0.DEVCMDSTAT.DCON = 0` produces a *downstream port 1* disconnect while
  the upstream link, the hub itself, and DEV1 on port 2 all stay up.
* Port resets are per-port (`hub_port_reset(0)` vs `hub_port_reset(1)`); only a
  genuine upstream `sync_busreset` would hit both. Re-enumerating DEV0 on port 1
  therefore cannot reset DEV1.

This is deliberately different from `caliptra_ss_usb_hs_dev_disconnect`, which
cycles VBUS and tears down the entire compound device. Here no VBUS cycling and
no testbench force is required - the firmware simply RMWs `DCON`.

## Test flow

Firmware (`caliptra_ss_usb_dual_device_hs_dev0_hotplug.c`):

1. Boot and configure both device controllers, enable both interrupt paths,
   assert `HUB_CONNECT`.
2. DEV1 runs a continuous EP1 OUT -> EP1 IN loopback service loop, re-arming
   EP1 OUT after every completed transfer.
3. A DEV0 hotplug FSM (`HP_WAIT_DEV1_UP -> HP_DISCONNECT -> HP_DISCONNECTED_HOLD ->
   HP_CONNECT -> HP_WAIT_REENUM -> ...`) performs `DEV0_TARGET_CYCLES`
   disconnect/reconnect iterations via `usb_set_device_connect()`.
   See [FSM terminology: "hold" vs "wait"](#fsm-terminology-hold-vs-wait) for
   why the two non-action states are named differently.
4. Two **isolation invariants** are checked continuously for DEV1:
   * DEV1 must never report `DEVCMDSTAT.DRES_C` once enumerated.
   * DEV1's `DEVCMDSTAT.DEV_ADDR` must never fall back to 0.
   A violation sets `dev1_isolation_violation` and the test reports FAILED.

Host side (`caliptra_ss_usb_dual_device_hs_dev0_hotplug_sequence.svh`):

1. Enumerate the hub, bring up port 1 and enumerate DEV0 (address 2), then
   bring up port 2 and enumerate DEV1 (address 3).
2. Baseline DEV1 EP1 bulk loopback.
3. For each hotplug cycle: arm a DEV1 OUT transfer, poll the hub's
   `GetPortStatus` for port 1 until `CURRENT_CONNECT_STATUS` clears, clear
   `C_PORT_CONNECTION`, complete and check the DEV1 IN transfer, then poll
   until port 1 reconnects and re-run port bringup + DEV0 enumeration.
4. Final DEV1 loopback plus a final DEV0 loopback to prove DEV0 is fully
   functional after the last reconnect.

If an expected port-1 connect-status edge never arrives the sequence raises a
`uvm_error`, so a missed hotplug event fails loudly rather than passing
vacuously.

## Constants that must stay in sync

| Location | Symbol | Value |
| --- | --- | --- |
| `*_sequence.svh` | `DEV0_HOTPLUG_CYCLES` | 3 |
| `*.c` | `DEV0_TARGET_CYCLES` | 3 |

## FSM terminology: "hold" vs "wait"

The hotplug FSM has two states in which the firmware takes no action, and they
end for completely different reasons. The distinction matters enough that the
names encode it, because conflating the two is what produced the earlier hangs.

| | ends on | duration | example |
| --- | --- | --- | --- |
| **HOLD** | a clock deadline | fixed, a *minimum residency* nothing external can shorten | `HP_DISCONNECTED_HOLD` |
| **WAIT** | an external event | unbounded above, as short as the event allows | `HP_WAIT_DEV1_UP`, `HP_WAIT_REENUM` |

A **hold** exists because the DUT must *remain* in some electrical condition
long enough for the other side to sample it. `HP_DISCONNECTED_HOLD` is the only
one here: DEV0 must stay detached for `DEV0_DISCONNECT_HOLD_US` so the host's
20 us hub-port poll cannot step straight over the disconnect edge and let the
test pass vacuously. It is *not* padding added to make something work - remove
it and the test stops proving anything.

A **wait** has no intended duration at all. `HP_WAIT_REENUM` ends the instant
the host has finished re-enumerating USBDC0 (observed as DEV0's EP1 being
re-armed), and carries no timer of its own - the host sequence already fails
loudly if port 1 never comes back, and the firmware's
`USB_TEST_RUN_BUDGET_US` is the global backstop.

The earlier names `HP_OFF_DWELL` / `HP_ON_DWELL` implied both were timed delays
bolted onto the sequence, which only the first one is.

## Simulation-time budget and how the run actually ends

The run does **not** end when the host sequence finishes. `phase_ready_to_end()`
in `caliptra_ss_usb_base_test` raises a `run_phase` objection and holds it until
`bfm_if.mcu_halt_status` asserts - i.e. until the **firmware** reaches
`csr_write_mpmc_halt()` at the end of `main()`. The MCU, not the sequence,
decides when the simulation stops.

That makes the firmware's loop ceiling a simulation-time control, and the
original one was not expressed in time at all: `USB_POLL_TIMEOUT` was a count of
**1500000 main-poll iterations**. One iteration is not a stable unit of time (its
cost depends on how many register reads and `VPRINTF`s it performs), and at the
observed 50-100 cycles per iteration that ceiling needed **180-375 ms** of
simulated time to expire. It was effectively infinite: the firmware never
printed a verdict, never halted, and the run only terminated via the objection
path.

Measured on that run:

| | |
| --- | --- |
| VCS end of simulation | 6929 us |
| last real activity | ~1400 us |
| dead tail | **5529 us, 80% of the run** |

Two changes bound this:

* **Firmware** - `USB_TEST_RUN_BUDGET_US = 3000` (3 ms), enforced against an
  `mcycle` deadline captured once before the main loop. `poll_count` survives
  only as a diagnostic and is never a termination condition. The host sequence's
  own worst case is ~2.3 ms, so the firmware always outlives it and records a
  PASSED / FAILED / TIMEOUT verdict, then halts - which drops the objection
  immediately instead of waiting it out.
* **Test** - `get_mcu_halt_timeout()` is overridden to **5 ms** (the base default
  is 100 ms). A firmware that somehow never halts now costs 5 ms, not 100 ms.

### Progress diagnostics

The periodic progress dump used to be gated on `poll_count % 50000 == 0`, which
**never fired once**: only a few thousand iterations execute inside the window
where anything happens, so the run produced zero diagnostic lines and the USBDC1
stall had to be reconstructed entirely from host-side transfer timestamps. The
dump is now on a 100 us `mcycle` cadence (`USB_PROGRESS_DUMP_US`) and also prints
USBDC1's EP0 OUT and EP1 OUT/IN command-status words:

```
MCU: [poll N] hp_state=.. dev0_cycles=.. armed=.. DEVCMDSTAT=0x.. | \
     dev1 loops=.. armed=.. lb_armed=.. addr=.. DEVCMDSTAT=0x.. \
     ep0out=0x.. ep1out=0x.. ep1in=0x.. intr_cnt=..
```

Those `Active` bits are the only thing that distinguishes "the host never sent
the OUT" from "the OUT landed but the firmware never noticed the completion",
and `ep0out` likewise separates "no SETUP arrived" from "EP0 was left
un-armed"; the host-side log cannot tell those apart.


## DEV0 disconnected hold (`DEV0_DISCONNECT_HOLD_US`)

How long the firmware holds DEV0 `DCON` low has to fit inside a window with
both a floor and a ceiling:

* **floor** - the hold must outlast the sequence's hub port-1 poll interval
  (`PORT_POLL_INTERVAL = 20 us`) so the host cannot miss the disconnect edge
  entirely and pass vacuously.
* **ceiling** - the hold must expire well before the host's *reconnect* poll
  budget is exhausted. That budget is `PORT_POLL_MAX_ATTEMPTS` (60) polls of
  (20 us interval + ~2.6 us `GetPortStatus` transfer), i.e. about **1356 us**
  measured from the moment the host observed the disconnect.

The hold is therefore expressed in **time**, as
`DEV0_DISCONNECT_HOLD_US = 200` (~10 host poll intervals), converted to MCU
cycles via `CALIPTRA_SS_CLK_FREQ` (which is in MHz, hence cycles-per-µs) and
enforced against an `mcycle` deadline captured in `HP_DISCONNECT`.

A raw loop count cannot honour that ceiling, because one main-poll iteration is
not a stable unit of time - its cost depends on how many register reads and
`VPRINTF`s that particular iteration performs. The earlier value of 40000
iterations was an unanchored guess that landed far past the ceiling: DEV0 `DCON`
fell at ~766 us and the hold had still not expired when the host sequence
finished at ~2269 us, so `HP_CONNECT` was never reached and `DCON` never went
back high at all. In the waveform
`caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.DEV0_USBREG_DEV_CONNECT`
simply drops once and stays low, and `DCON set (port 1 up)` never prints. The
resulting

```
Hub port 1 never reached CONNECT_STATUS=1 within 60 polls (reconnect_cyc0)
```

is therefore not a missed edge but a reconnect the firmware never performed -
which is why the `HP_WAIT_REENUM` side carries no timeout of its own: the host
sequence already fails loudly if port 1 never returns, and the main loop has its
own `USB_TEST_RUN_BUDGET_US` backstop.

## Post-port-reset settling (`POST_PORT_RESET_SETTLE`)

A hub downstream port reset propagates a USB bus reset into the device
controller behind it, and the IP_3511 clears the Active bit on *every* endpoint
entry when it sees one. The device NAKs all tokens until firmware notices
`DEVCMDSTAT.DRES_C` and runs `usb_handle_bus_reset()` -> `usb_ep0_reinit()`.
USB 2.0 section 8.5.3 forbids NAKing a SETUP, so a SETUP that lands inside that
re-arm window is reported by the VIP as
`valid_device_response_check` ("Received a NAK device response to a host SETUP
packet which is a violation") even though its retries eventually succeed.

This is a **firmware-latency** effect, not a line-speed effect.
`hub_port_bringup_stepB()` in the base sequence waits 10 us after the reset,
which is sufficient for the plain HS dual-device loopback test. It is not
sufficient here because this firmware services *both* controllers from a single
polling loop *and* runs the DEV0 hotplug FSM in that same loop, so one
controller's `DRES_C` handling can queue behind the other's servicing.

The sequence therefore waits an additional `POST_PORT_RESET_SETTLE = 80 us`
(about ten HS microframes) after every port bring-up and before enumerating the
device behind that port. The FS variant of this problem needs a much larger
value only because an FS frame is 1 ms.

## Bus-reset handling: why `DRES_C` is sampled once before anything can clear it

This shares its root cause with the EP0 section below: a *sticky hardware status
bit* must be read before any helper that consumes it, and must never be hidden
behind a *losable interrupt event*.

This issue was found by a Copilot review comment raised against the FS
dual-device bulk loopback test ("DRES_C is consumed before the EP1 reset
handling runs"). The identical pattern was present here, and the consequences
were worse, so the finding was ported over.

### The consumed-bit mechanism

`usb_handle_bus_reset()` in `libs/usb/usb.c` is *self-guarded and
self-clearing*:

```c
void usb_handle_bus_reset(void) {
    uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
    if (!(cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK)) {
        return;                 // no reset pending -> do nothing
    }
    ...
    usb_devcmdstat_write(cmd | DEV0_CSR_DEVCMDSTAT_DRES_C_MASK);   // W1C
    usb_ep0_reinit();
    ...
}
```

The earlier version of `usb_service_device()` called it *unconditionally* as its
first action, and only afterwards tested `DRES_C` itself:

```c
usb_handle_bus_reset();                       // clears DRES_C here

if (usb_events & DEV0_CSR_INTSTAT_DEV_INT_MASK) {
    uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
    if (cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {   // can never be true
        ...
    }
}
```

The inner block was therefore **dead code** on every iteration.

### The two silent consequences

1. **Stale EP1 state.** A bus reset makes hardware clear `Active` on every
   endpoint entry, but `ep1_armed` / `loopback_armed` were never cleared, so the
   firmware kept believing EP1 was armed and waited forever on a disarmed
   endpoint.
2. **The headline assertion of this test could not fire.** The
   `dev1_isolation_violation` check lived inside that dead block. A genuine
   isolation failure - USBDC1 seeing a bus reset caused by DEV0's hotplug -
   would have been reported as a **PASS**. A test that cannot fail is worse than
   no test at all.

### The fix

Sample `DEVCMDSTAT` once, then do all reset work inside that one branch:

```c
{
    uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);

    if (cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
        if (dev == 1 && st->enumerated) {
            dev1_isolation_violation = true;
            ...
        }
        usb_handle_bus_reset();         // restores EP0 and W1C-clears DRES_C
        st->ep1_armed      = false;
        st->loopback_armed = false;
    }
}
```

Two deliberate properties:

- **No `DEV_INT_MASK` gate.** `DRES_C` is sticky; the interrupt event is not.
  With DEV0 (PIC vector 3) and DEV1 (PIC vector 6) at *equal* priority the two
  controllers' events serialise rather than preempt, so a one-shot event can be
  missed entirely. The sticky bit cannot. Same reasoning as the EP0 gate below.
- **EP1 state is cleared unconditionally**, not under `if (st->ep1_armed)`.
  Hardware has already disarmed everything; the firmware's job is only to agree
  with it.

Do not reintroduce a call to `usb_handle_bus_reset()` anywhere earlier in the
poll loop, and do not move the isolation check behind an interrupt-event test.

## EP0 servicing: why it is driven off hardware truth, not the interrupt event


EP0 control transfers are serviced from **`DEVCMDSTAT.SETUP`** (bit 8), **not**
from `INTSTAT.EP0OUT` latched into the foreground mailbox. This is not a style
preference - the event-gated form deadlocks, and it did so in this test.

The EP0 OUT `Active` bit (`usb_ep0_out_unarmed()`) is used only as a secondary
re-arm condition. **The two signals are not interchangeable**; see
[Why the gate is `DEVCMDSTAT.SETUP` and not the EP0 OUT `Active` bit](#why-the-gate-is-devcmdstatsetup-and-not-the-ep0-out-active-bit)
below, where swapping them produced a worse deadlock.


### The deadlock chain

1. The two controllers sit on **equal-priority PIC vectors** - DEV0 on
   `cptra_ss_mcu_ext_int[3]` and DEV1 on `cptra_ss_mcu_ext_int[6]`, both at
   priority 7. Equal priority means they **serialize** rather than preempt, so
   one device's ISR can run while the other device's event is pending.
2. The ISR W1C-acknowledges `INTSTAT` unconditionally. If the acknowledge lands
   between hardware asserting the bit and the ISR ORing it into the foreground
   mailbox - or if `main()` snapshots and clears the mailbox in the same
   iteration the bit was set - the **single** `EP0OUT` event for that packet is
   lost.
3. The SETUP packet is still sitting in the SETUP buffer and EP0 OUT is left
   **un-armed**. An un-armed EP0 OUT is exactly the condition under which the
   controller **NAKs** the next incoming SETUP. A NAK generates no new `EP0OUT`
   event, so with event-gated servicing **EP0 can never recover**.

This is the same failure class as the EP1 `Active` two-phase livelock
documented below: a one-shot event used as the only gate on forward progress.

### Round-8 evidence

DEV1's enumeration died exactly one SETUP short of DEV0's:

| MCU time (ns) | DEV0 (worked) | DEV1 (stalled) |
|---|---|---|
| | 522057 `bReq=0x6` GET_DESCRIPTOR | 669495 `bReq=0x6` GET_DESCRIPTOR |
| | 527577 `bReq=0x0` GET_STATUS | 674940 `bReq=0x0` GET_STATUS |
| | 532982 `bReq=0x5` SET_ADDRESS -> 2 | 680310 `bReq=0x5` SET_ADDRESS -> 3 |
| | 540610 `bReq=0x6` GET_DESCRIPTOR | 694617 `bReq=0x6` GET_DESCRIPTOR |
| | 546025 `bReq=0x8` GET_CONFIGURATION | 699347 `bReq=0x8` GET_CONFIGURATION |
| | 551460 `bReq=0x9` SET_CONFIGURATION | **never arrives** |
| | 555990 `dev0 EP1 OUT armed` | - |
| | 557600 `dev0 enumerated (addr=2)` | - |

After mcu 699347 ns no further SETUP of any kind was serviced. `intr_cnt` froze
at **35** across every progress dump from 785370 ns to 1285610 ns, with
`loops=0 armed=0 lb_armed=0 addr=3 hp_state=0`. The UVM side reported
`valid_device_response_check_Dev3_EP0` - "Received a NAK device response to a
host SETUP packet" - at sim 693003 ns, which maps through the ~7240 ns
mcu-console offset to mcu ~685763 ns, i.e. ~463 ns after a progress dump began
printing across both apertures.

Consequence: because SET_CONFIGURATION never ran, `usb_is_configured()` stayed
false for DEV1, EP1 was never armed, `loop_count` stayed 0, `HP_WAIT_DEV1_UP`
never released, and `dev0_cycles` stayed 0 - **the DEV0 hotplug cycling that is
the entire point of this test never started.**

### Why the gate is `DEVCMDSTAT.SETUP` and not the EP0 OUT `Active` bit

The first attempt at this fix used `usb_ep0_out_unarmed()` as the outer gate.
That is **wrong**, and it produced a worse deadlock than the one it replaced.

A SETUP packet is written to the controller's **dedicated SETUP buffer**. It
does **not** consume the EP0 OUT arm, so EP0 OUT's `Active` bit **stays set**
while the SETUP waits to be decoded. Gating on "EP0 OUT is un-armed" therefore
locks out `usb_handle_control_transfer()` for exactly as long as there is a
SETUP to service - i.e. forever, starting from the very first SETUP of
enumeration.

A single round-9 progress-dump line at 587900 ns shows both bits at once:

| field | value | bit | meaning |
|---|---|---|---|
| `DEVCMDSTAT` | `0x10810B80` | 8 (`SETUP`, mask `0x100`) **set** | a SETUP is pending |
| `ep0out` | `0x80004005` | 31 (`Active`) **set** | EP0 OUT is still armed |

Both controllers sat in that state for the whole run: `addr` stayed 0, no
controller ever enumerated, `intr_cnt` moved 6 -> 8 and then froze, and the
firmware burned its entire 3000 us budget reporting
`dev0_cycles=0/3 dev1_loops=0/5 polls=5161`. Round 8 at least got DEV0
enumerated; this broke both.

### The fix

```c
uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
if (cmd & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) {
    usb_handle_control_transfer();   // decodes the SETUP and re-arms EP0
} else if (usb_ep0_out_unarmed()) {
    usb_ep0_arm_out();               // idempotent
}
```

`DEVCMDSTAT.SETUP` is checked **unconditionally**. It is a hardware status bit
that stays set until `usb_handle_control_transfer()` W1C-clears it, so it does
not depend on the `EP0OUT` interrupt event ever reaching the mailbox - which is
what fixes the round-8 lost-event deadlock. A lost interrupt now costs **one
extra poll iteration** instead of the endpoint.

The un-armed test survives only as the **secondary** case: with no SETUP
pending, an un-armed EP0 OUT means a control-read status-stage ZLP OUT completed
(or its event was lost), and re-arming keeps the next SETUP from being NAK'd.

Three things must not be changed:

* **do not** re-gate this block on `usb_events & DEV0_CSR_INTSTAT_EP0OUT_MASK`
  (round-8 deadlock);
* **do not** make the `SETUP` check conditional on `usb_ep0_out_unarmed()`
  (round-9 deadlock);
* **do not** swap the branch order.


### Diagnostics

The DEV1 progress dump prints the raw EP list entries - `ep0out=`, `ep1out=`,
`ep1in=` - alongside `DEVCMDSTAT` and `intr_cnt` precisely so that an arm/
complete stall can be attributed to hardware state rather than inferred from
interrupt bookkeeping.

## EP0 OUT re-arm: why this test does not use `usb_ep0_arm_out()`

This test deliberately re-arms EP0 OUT through its own local helper,
`usb_ep0_arm_out_sized()`, instead of the shared library's
`usb_ep0_arm_out()`. **Do not "simplify" this back to the library call.**

### The two disagreeing library paths

`libs/usb/usb.c` arms the EP0 OUT list entry in two places, and they do not
write the same thing:

```c
void usb_ep0_reinit(void) {                       /* bus-reset path */
    uint32_t ep0_out_entry = USB_EP_ENTRY_ACTIVE
                           | USB_EP_ENTRY_NBYTES(8)                 /* <-- present */
                           | USB_EP_ENTRY_ADDR(USB_SRAM_EP0_OUT_BUF_OFFSET);
    ...
}

void usb_ep0_arm_out(void) {                      /* steady-state path */
    uint32_t ep0_out = USB_EP_ENTRY_ACTIVE
                     | USB_EP_ENTRY_ADDR(USB_SRAM_EP0_OUT_BUF_OFFSET);
    ...                                                             /* NBytes omitted */
}
```

`usb_ep0_arm_out()` is called from roughly seven sites inside
`usb_handle_control_transfer()`, so the very first control transfer after a bus
reset silently rewrites the entry with a **zero-length** buffer.

### Entry decode

`NBytes` is bits `[25:11]`; `ADDR` is `[10:0]` in 64-byte units.

| Raw entry | `Active` | `NBytes` | `ADDR` | Meaning |
|---|---|---|---|---|
| `0x80004005` | 1 | 8 | `0x005` -> `0x140` | correctly armed for an 8-byte SETUP data phase |
| `0x80000005` | 1 | 0 | `0x005` -> `0x140` | *looks* armed, but can accept 0 bytes |

A zero-length EP0 OUT cannot absorb the 8-byte data phase of a SETUP, so the
controller **NAKs the SETUP** - which USB 2.0 section 8.5.3 forbids. The VIP
flags this as `valid_device_response_check_Dev<addr>_EP0`.

### Why this hid for several rounds

The `Active` bit stays **set** in the broken entry. Every "is EP0 armed?"
heuristic - including this test's own `ep0out=` progress dump and the original
`usb_ep0_out_unarmed()` - therefore reported a perfectly healthy, armed
endpoint while the endpoint was in fact useless. The decay is only visible if
you look at the `NBytes` field.

The DEV1 `ep0out` column in `mcu_console.log` shows it directly:

| MCU time | `ep0out` | `intr_cnt` | State |
|---|---|---|---|
| 580507.5 ns | `0x80004005` | 21 | armed with NBytes = 8, enumeration progressing |
| 684890.0 ns | `0x80000005` | 30 | NBytes lost right after `SET_ADDRESS addr=3` |
| 785352.5 ns | `0x80000005` | 33 | permanently stuck, device never configured |

### The fix, and why it is local

```c
#define USB_EP0_OUT_NBYTES_FIELD  USB_EP_ENTRY_NBYTES(0x7FFFu)
#define USB_EP0_OUT_SETUP_NBYTES  8u

static void usb_ep0_arm_out_sized(void) {
    uint32_t entry = USB_EP_ENTRY_ACTIVE
                   | USB_EP_ENTRY_NBYTES(USB_EP0_OUT_SETUP_NBYTES)
                   | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR
                                           + USB_SRAM_EP0_OUT_BUF_OFFSET);
    lsu_write_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP0_OUT_OFFSET, entry);
}
```

`usb_ep0_out_unarmed()` was also widened to treat `Active`=1 with `NBytes`=0 as
un-armed, so the re-arm actually fires.

This is a **pre-existing defect in the shared library, not a regression from
any fix in this test**. It only bites tests that re-arm EP0 repeatedly; the
single-shot loopback tests complete enumeration before the decay matters, which
is why they never showed it. The override is kept inside this test to contain
the change rather than perturbing every existing USB test. **If
`usb_ep0_arm_out()` is ever corrected in `libs/usb/usb.c`, delete
`usb_ep0_arm_out_sized()` and call the library function again.**

## EP1 loopback handshake: difference from the dual-device bulk loopback reference



`caliptra_ss_usb_dual_device_hs_bulk_loopback` performs exactly **one** EP1
loopback per controller and latches it with a sticky `done` flag. That lets it
drive the OUT -> IN copy straight off the mailbox `INTSTAT.EP1OUT` event bit:
a stale or spurious event can only ever fire once, before any payload matters.

This test re-arms EP1 OUT **repeatedly** for USBDC1, so that window re-opens on
every iteration. `usb_ep1_out_arm()` sets `INTEN.EP1OUT` without first clearing
a pending `INTSTAT.EP1OUT`, so a left-over event bit makes the copy run while
the EP1 OUT buffer is still empty. EP1 IN is then armed with zeros and
`loopback_armed` is already set, so the block is skipped when the real OUT data
finally lands - the host's BULK IN reads back 64 zero bytes. This is exactly the
`USBDC1_baseline loopback mismatch ... received=0x00` failure mode.

The fix is to drive both halves of the handshake off the EP command/status list
`Active` bit (bit 31) rather than the mailbox event bit, because that bit is
hardware truth:

* `usb_ep1_out_complete()` - EP1 OUT `Active` cleared means the received bytes
  really are in the buffer, so the OUT -> IN copy is safe.
* `usb_ep1_in_complete()` - EP1 IN `Active` cleared means the host has actually
  drained the IN payload, so the iteration can be counted and EP1 OUT re-armed.

### Why this is a *single-phase* check, and must stay that way

The EP-list lives in the controller's packet SRAM and the arming store is
posted, so a load performed in the *same* poll iteration as the arming write can
still return the pre-arm value - `Active == 0` - and be mistaken for a
completion that never happened.

The obvious-looking guard against that is a two-phase edge: require `Active` to
be **observed set** before accepting a clear as a completion. **That is a
livelock.** Hardware only ever *clears* `Active`; it never sets it - only
firmware does, when it arms the entry. So if the very first read misses the set
state (either because the posted EP-list write had not landed yet, or because
the host had already completed the transfer and hardware had already cleared the
bit), the "observed set" condition can never be satisfied again and that
endpoint is never recognised as complete for the rest of the run.

That is precisely what stalled USBDC1 in hotplug cycle 0:

| time | event |
| --- | --- |
| 771610 ns | `MCU: dev1 EP1 OUT armed` |
| 782266 ns | host's `HS_BULK_OUT_EP1_dev1_cyc0` completed |
| - | `MCU: dev1 EP1 IN armed (loopback)` **never printed** |
| 787080 ns | `ClearFeature_C_PORT_CONNECTION_Port1_disconnect_cyc0` completed |
| 807080 ns | `HS_BULK_IN_EP1_dev1_cyc0` issued (exactly +20 us, so `POST_BULK_OUT_SETTLE` *was* applied) |
| 812681 ns | `USBDC1_dev0_down_cyc0 loopback check FAILED: received 0 of 64 bytes` |

The BULK IN hit an endpoint the firmware had never armed, so it was NAKed and
came back empty. The settle wait was correctly applied, which rules out timing:
no amount of waiting recovers a firmware state machine that has stopped
advancing.

The correct way to cover the posted EP-list write is to confirm the arm **at arm
time**, not at completion time. `usb_ep1_confirm_armed()` is called at the end
of both `usb_ep1_out_arm()` and `usb_ep1_loopback_arm_in()` and re-reads the
entry until `Active` is observed set (bounded by `USB_EP_ARM_CONFIRM_LIMIT`,
which warns rather than hangs if a controller is genuinely unresponsive). With
the arm confirmed visible before the function returns, a later cleared `Active`
is unambiguously a completion and both gates are plain single-phase tests. The
per-device state is therefore just `ep1_armed` / `loopback_armed`, cleared
wherever the arm state is torn down: the `DRES_C` bus reset branch, the
enumeration re-arm branch, and `HP_DISCONNECT`.

## EP1 data-toggle reset on every re-arm (`USB_EP_ENTRY_TOGGLE_RESET`)

The dual-device bulk-loopback reference performs exactly ONE EP1 OUT and ONE
EP1 IN per controller, so its endpoint data toggle only ever has to start from
DATA0 - and a bus reset already guarantees that (`reg_ep_toggle_value` is
cleared on `sync_busreset` in `usb_reg_if.m.vhdl`).

This test re-arms the SAME EP1 OUT/IN many times. Two things then collide:

* the device keeps alternating DATA0/DATA1 across iterations, as bulk endpoints
  must;
* the host side does not follow that, because every USBDC1 transfer is preceded
  by `host_agent_h.reconfigure()` to retarget the single remote-device model,
  and that resets the VIP's toggle expectation back to DATA0.

The symptom was:

```
data_toggle_check_Dev3_EP1_IN: Received Data packet with incorrect PID
name : DATA1. Expecting DATA0 for DATA stage
```

The fix is to arm each EP1 command/status entry with the TR (Toggle Reset) bit,
bit 28, exposed as `USB_EP_ENTRY_TOGGLE_RESET` in `libs/usb/usb.h`. The RTL
latches it straight out of the entry word the DMA engine fetches
(`usb_ep_config_handler.m.vhdl`):

```vhdl
reg_ep_toggle_reset(epconfig_link) <= upd_dma_wdata(28);
```

and `usb_ep_config_hub_pkg.p.vhdl` places the vector back into the per-endpoint
info word at bit 28. With TR set on every re-arm, each iteration starts from the
DATA0 state the host expects.

## EP1 handshake settling (`PRE_BULK_OUT_SETTLE`, `POST_BULK_OUT_SETTLE`)

The firmware services both controllers AND runs the DEV0 hotplug FSM from a
single polling loop, so its EP1 re-arms are several microseconds behind the
events that trigger them. Two named settle constants in the sequence cover that
latency; both are 20 us.

* `PRE_BULK_OUT_SETTLE` - waited before every USBDC1 EP1 BULK OUT. The firmware
  only re-arms EP1 OUT after it has seen the previous EP1 IN complete. Without
  the wait the OUT was issued first and sat NAKing for ~55 us:

  ```
  740416 ns  DATA HS_BULK_OUT_EP1_dev1_cyc0 issued
  744325 ns  MCU: dev1 EP1 OUT armed for 64 bytes
  795115 ns  Transfer HS_BULK_OUT_EP1_dev1_cyc0 completed
  ```

  which lengthens the run and skews the USBDC1-traffic / USBDC0-hotplug overlap
  the test is built around.

* `POST_BULK_OUT_SETTLE` - waited between an EP1 BULK OUT completing and the
  matching EP1 BULK IN. The firmware copies EP1 OUT -> EP1 IN and arms EP1 IN
  only after polling the EP1 OUT entry and seeing its `Active` bit clear.
  `dev1_loopback()` always waited here, but the hotplug-cycle path originally
  relied on the hub port-1 poll plus `ClearFeature` to provide the gap, and that
  only covered ~4.8 us:

  ```
  782266 ns  Transfer HS_BULK_OUT_EP1_dev1_cyc0 completed
  785083 ns  Hub port 1 reached CONNECT_STATUS=0
  787080 ns  DATA HS_BULK_IN_EP1_dev1_cyc0 issued
  792882 ns  Transfer HS_BULK_IN_EP1_dev1_cyc0 completed
  ```

  with no `MCU: dev1 EP1 IN armed (loopback)` in between. The IN therefore hit
  an un-armed endpoint, was NAKed, and returned an EMPTY payload - which reads
  back as 64 zero bytes and looked like data corruption rather than a handshake
  race. All three OUT -> IN turnarounds (baseline/final `dev1_loopback()`,
  hotplug step 6c, and the DEV0 final loopback) now use this constant.

To keep that class of failure from being misread again, `check_loopback()`
validates `payload_byte_count()` BEFORE the per-byte compare and reports a
short/empty payload as a single targeted error instead of 63 byte mismatches.

## Round 10: the progress dump was the bug, and the test could not fail

This round was driven entirely from `vcs_sim.log` (no waveform needed) and it
found **two independent defects**: one that caused the failure, and one that
hid it.

### Defect 1 - the diagnostic was the blocking agent

The reported symptom was three copies of:

```
valid_device_response_check_Dev3_EP0 ... Received a NAK device response to a
host SETUP packet which is a violation
```

Evidence assembled from the log:

| Observation | Source | Meaning |
|---|---|---|
| All four `D_adr=3` control transfers show `ABORTED`, `Pld Size = 0` | VIP `prot_mon.HS.xfer_trace` | DEV1 enumeration never moved a single payload byte |
| DEV0 (`adr 2`) shows `GET_DESCRIPTOR Pld 18 ACCEPT`, `GET_CONFIGURATION Pld 1 ACCEPT` | same | the mechanism works; DEV1 specifically was starved |
| Last DEV1 SETUP serviced at 684357 ns (`SET_ADDRESS addr=3`), next at 698352 ns | MCU console | a **14.0 us SETUP-servicing dead zone** |
| `bReq=0x8` (GET_CONFIGURATION) and `bReq=0x9` (SET_CONFIGURATION) never appear for DEV1 | MCU console | those two SETUPs were dropped, not mishandled |
| Progress dump at 693082 ns: `DEVCMDSTAT=0x10814B83` (bit 8 SETUP set), `addr=3`, `ep0out=0x80004005` (Active, NBytes=8 - **no decay**) | MCU console | the hardware was healthy the whole time |
| 693082 -> 698352 ns is 5270 ns; the dump is ~184 characters at ~28.6 ns/char | arithmetic | **the dump itself consumed the dead zone** |

`VPRINTF` writes one character at a time to
`SOC_MCI_TOP_MCI_REG_DEBUG_OUT`. At `CALIPTRA_SS_CLK_FREQ = 400` that measures
about 28.6 ns per character, so the two-line progress dump is a ~5.3 us window
in which the MCU services nothing. The host spaces enumeration SETUPs about
5 us apart, so one dump landing inside enumeration is sufficient, on its own,
to drop a SETUP and earn the NAK-to-SETUP violation.

Because `USB_PROGRESS_DUMP_US` is `mcycle`-anchored and the simulation is
deterministic, the dump landed at the same phase on every run - which is
exactly why the failure reproduced identically round after round, and why
trial-and-error on unrelated constants never moved it. DEV0 survived only by
luck of phase.

Note the irony: rounds 8 and 9 added the dump specifically to gain visibility,
and the dump then became the defect. **A diagnostic that costs 5 us per sample
is not free on a 5 us protocol.**

### Defect 2 - the test could not fail

Independently of the above, the sequence reported success on a run in which
nothing worked:

* `wait_xfer_done()` never inspected `svt_usb_transfer::status`, so four
  `ABORTED` transfers produced **zero** sequence errors.
* `check_device_address()` ran its comparison on a zero-payload transfer and
  printed `dev1 device address checked (expected=3 got=3)` - a vacuous pass.
* The sequence printed `Dual-device enumeration complete (USBDC0@2, USBDC1@3)`
  at 695232 ns, after DEV1 had failed every one of its control transfers.

The only reason the run was marked failing at all is that the VIP's own
protocol checker fired. Every test-authored check passed.

### Net consequence

dev1 never configured -> EP1 never armed -> `dev1 loops=0` ->
`HP_WAIT_DEV1_UP` never released -> `hp_state=0`, `dev0_cycles=0/3`. **The DEV0
hotplug cycling that is the entire purpose of this test has never executed
once**, in this round or any previous one. All hotplug constants
(`DEV0_DISCONNECT_HOLD_US`, `POST_PORT_RESET_SETTLE`, the reconnect budget)
remain unvalidated by execution.

### Fixes implemented

**Track A - make the test capable of failing** (prerequisite for trusting any
later experiment):

* `caliptra_ss_usb_base_sequence.svh`: added `check_xfer_status()` and
  `wait_and_check_xfer()`. These error on a null item, on
  `status != svt_usb_transfer::ACCEPT`, on any non-zero bit in
  `results_status`, and on `payload_byte_count()` below a per-step minimum.
* All seven control steps in `usbdc0_enum_stepC()` now use
  `wait_and_check_xfer()` with explicit payload minimums (18 for the device
  descriptor, 2 for `GET_STATUS`, 1 for `GET_CONFIGURATION`, 0 for the
  no-data-stage writes).
* `caliptra_ss_usb_data_check_api_impl.svh`: `check_device_address()` now
  rejects a transfer that is not `ACCEPT`, that has a non-zero
  `results_status`, or that moved zero payload bytes - instead of comparing
  against stale/empty data and passing.

**Track B - stop the diagnostic from breaking the protocol:**

The progress dump is now gated on **both**

1. `dev0_cycle_count > 0` - completely silent until the first hotplug cycle has
   completed, which is after all enumeration, and
2. no `DEVCMDSTAT.SETUP` pending on either controller (via
   `usb_ep0_setup_pending()`) - keeps it out of the USBDC0 re-enumeration
   windows that occur after every reconnect.

When deferring, `next_dump` is deliberately **not** re-armed, so the dump fires
on the first subsequent control-traffic-free iteration rather than slipping a
whole cadence period.

**Track C - decouple control latency from loop cost:**

The EP0 SETUP/re-arm logic moved out of `usb_service_device()` into a new
`usb_service_ep0(int dev)`, and `main()` now runs an **EP0-only pass over both
controllers as the very first thing in each iteration**:

```c
usb_service_ep0(0);
usb_service_ep0(1);

usb_service_device(0, ev0, &dev_state[0]);
usb_service_device(1, ev1, &dev_state[1]);
```

SETUP service latency is now bounded by a handful of register accesses per
controller instead of by whatever the rest of the iteration happens to cost.
`usb_service_device()` still calls `usb_service_ep0(dev)`; the function is
idempotent and that second call is a no-op once the SETUP has been drained.
The two branches inside it keep their original order and remain unconditional -
see the round-8 / round-9 notes above for why that must not change.

### What to look for in the next run

* If the latency problem persists, the run now fails **loudly and early**
  (~685 us) on the `ABORTED` `GET_DESCRIPTOR` for Dev3, naming the transfer -
  instead of limping to a vacuous "enumeration complete".
* On success: `dev1 enumerated (addr=3)`, `dev1 EP1 bulk loopback #1 complete`,
  `dev1 up and looping - starting DEV0 hotplug cycles`, and `dev0_cycles`
  becoming non-zero **for the first time ever**.
* Only once `dev0_cycles` advances is it meaningful to tune the hotplug timing
  constants. Treat any hotplug-timing hypothesis before that point as
  unfalsifiable.

## Note on concurrency

The SVT USB VIP is configured with a single remote device
(`local_device_cfg_size = 1`), so the host must re-anchor
`remote_device_cfg[0].device_address` (and call `reconfigure()`) before talking
to a different address. DEV1 data transfers and hub port-1 status polls are
therefore *interleaved at transfer granularity* rather than forked. The
hardware-level simultaneity being tested is still real: DEV1's endpoint stays
armed and its transfer in flight across the port-1 drop; only the host-side
observation is serialized.

## Build / enable requirements

Both of these are required and are set in the test `.yml`:

* `BUILD_CFLAGS="-DUSB_HUB_COMPOUND_DEV1_IRQ"` - firmware-side DEV1 interrupt
  handling.
* `+USB_HUB_COMPOUND_DEV1_IRQ=1` - testbench-side loopback of
  `cptra_ss_usb_dev1_irq_o` onto `cptra_ss_mcu_ext_int[6]`.

The image must **not** be built with `-DUSB_DEV_SEL=1`; it targets both
controllers at runtime through `usb_select_device()`.

## Run

```sh
make -f $CALIPTRA_SS_ROOT/tools/scripts/Makefile \
     TESTNAME=caliptra_ss_usb_dual_device_hs_dev0_hotplug ...
```

or via the regression lists in
`src/integration/stimulus/L1_Nightly_Directed_caliptra_ss_top_tb_regression.yml`
and `..._Strict_...yml`, where the test is registered.

<!-- File contains AI-generated response based on internal company sources -->
