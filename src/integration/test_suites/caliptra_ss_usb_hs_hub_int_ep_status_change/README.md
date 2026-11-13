# caliptra_ss_usb_hs_hub_int_ep_status_change

Hub **status-change interrupt endpoint (EP1 IN)** polling test for the USB 2.0
compound device (embedded virtual hub + two software device controllers),
running at **High Speed**.

Stimulus for coverage gap **G1** of `docs/usb_coverage_gaps.md`.

## Intent

The hub reports downstream port events to the host on its interrupt endpoint,
exactly as USB 2.0 chapter 11 requires. No test in the repo had ever polled it:
every other hub test drives EP0 control transfers only. The consequence,
measured on the nightly merge, is that `USB_APP_HW_HUB` sits at **12.64% toggle**
with `HUB_EPIN_REQ` / `HUB_EPIN_GNT` / `HUB_EPIN_RDATA` / `HUB_EPIN_STALL` at
**0%**, and physical endpoint slot `[0]` of `USB_EP_CONFIG_HANDLER`
(`REG_EP_ACTIVE[0]`, `NBYTES_UPDATE_TOGGLE*`, `EP_SET_ENABLE_TOGGLE*`) never
sees a single `0 -> 1` transition.

This test drives real **INTERRUPT IN** tokens at the hub, which is the only way
to reach that logic.

## What is checked

For each of three different port change events the test requires **both**:

1. the change bit to appear in the `GetPortStatus` word (EP0, the status plane),
   and
2. the matching bit to come back in the **status-change bitmap on EP1 IN** (the
   data plane).

Check 2 is the load-bearing one. Check 1 alone only proves the hub latched its
own bookkeeping; only check 2 forces the hub to arm the endpoint, win the DMA
grant and return data.

A fourth leg polls EP1 IN **once** with **every change bit acknowledged** and
requires that no data comes back, so a hub that armed the endpoint
unconditionally would fail rather than pass all three positive legs by accident.

| Leg | Event driven | Port status bit | EP1 IN bitmap |
|---|---|---|---|
| connectChange | DCON asserted by firmware during boot | 16 `C_PORT_CONNECTION` | bit 1 set |
| resetChange   | `SetPortFeature(PORT_RESET)` port 1    | 20 `C_PORT_RESET`      | bit 1 set |
| suspendChange | `SetPortFeature` then `ClearPortFeature(PORT_SUSPEND)` port 1 | 18 `C_PORT_SUSPEND` | bit 1 set |
| idle | nothing outstanding | - | **no data** (NAK) - currently FAILS, see Status |

## Status

**The three positive legs pass. The idle leg (step 7) is an EXPECTED FAILURE
against the current RTL.**

The three positive legs each return bitmap `0x02` (bit 1 = port 1) at
366114 / 397196 / 438728 ns, so coverage gap G1 is closed by this test
regardless of the idle leg.

On the idle leg the hub answers the first EP1 IN token with one byte of `0x00`
even though `GetPortStatus` reports `wPortChange = 0x0000`. The designer
confirmed that the hub is required to NAK **already on that first token**, so
this is an RTL issue and the test is left failing to track it. The idle leg is
deliberately **last**, so its failure cannot mask the legs that close the gap,
and it can be disabled with `CHECK_NAK_LEG = 0` in the sequence if it becomes
regression noise before the RTL is fixed.

## Mechanism (MEASURED from the RTL)

`usb_app_hw_hub.m.vhdl`, with `C_HUB_NB_PORTS = 2` and `C_DATAWIDTH = 64` in
this integration:

```vhdl
-- GEN_HUB_STATUS_EP1 (414-421)
hub_port_status_change(i) <= '1' when hub_port_l1_change(i)      = '1' or
                                      hub_port_reset_change(i)   = '1' or
                                      hub_port_suspend_change(i) = '1' or
                                      hub_port_connect_change(i) = '1'
                                 else '0';

-- PROC_EPIN_ACTIVE (425-433) : this is what ARMS the endpoint
hub_epin_enable_buffer <= hub_dev_status_change or (any hub_port_status_change)

-- PROC_HUB_EPIN_DATA (441-459) : the returned bitmap
hub_epin_rdata_buffer(0) <= hub_dev_status_change;        -- hardwired 0 (line 423)
hub_epin_rdata_buffer(2 downto 1) <= hub_port_status_change;

-- line 437
hub_epin_buffer_size <= ((C_HUB_NB_PORTS+1)/8)+1;         -- = 1 byte
```

So the bitmap is **one byte**, laid out `{0,0,0,0,0, port2, port1, hub}`, and the
port under test (port 1) is **bit 1**. `hub_dev_status_change` is tied to 0 by
the designer, since this hub has no overcurrent detection and no local power
source change, so bit 0 can never be set.

The connect edge comes from the firmware without any extra work:

```vhdl
hub_port_connect(0) <= dev0_usbreg_dev_connect;   -- DEV0 DCON = hub port 1
```
(`ip_xxx_3511_hs_mem_compound_structure.a.vhdl` line 2357), and
`boot_usb_core_hub()` sets `DEVCMDSTAT.DCON` during bring-up.

## Why the step order is not negotiable

Lines 328-342 force `suspend_change`, `reset_change` and `l1_change` back to 0
on **every clock** unless the port is both connected *and* enabled:

```vhdl
if hub_port_connect(i) = '0' then        -- clear suspend / l1 / reset change
elsif hub_port_enable_int(i) = '0' then  -- clear suspend / l1 / reset change
```

The port is only enabled by `SetPortFeature(PORT_RESET)` (lines 280-282 raise
`hub_port_reset_int` and `hub_port_enable_int` together), so:

* the **reset** leg must come before the **suspend** leg, and
* driving `ClearPortFeature(PORT_SUSPEND)` on a still-disabled port would latch
  `suspend_change` for less than a clock and the poll would see nothing. That
  would look like an RTL bug; it would be a stimulus ordering mistake.

`connect_change` is the exception: set on **any** edge of `hub_port_connect`
(lines 202-203) and **not** in the force-clear list, so it survives
`connect = 0`. It is therefore read first, before anything acknowledges it.

Two further RTL details the sequence follows rather than fights:

* `suspend_change` is set by the **Clear** of `PORT_SUSPEND` (line 233), not by
  the Set - the same spec-correct behaviour documented in
  `caliptra_ss_usb_hs_dev_hub_port_suspend`.
* `reset_change` needs `reset_int` and `enable_int` in the same cycle, and
  `reset_int` is only one clock wide (line 198), so `SetPortFeature(PORT_RESET)`
  is the only request that can produce it.

## Side effects, stated plainly

`SetPortFeature(PORT_RESET)` on port 1 bus-resets **USBDC0**, returning it to
address 0. This is deliberate and is the only way to produce `reset_change`. The
sequence never addresses USBDC0, so nothing downstream of that reset is relied
upon; the firmware services the resulting `DEVCMDSTAT.DRES_C` in its normal
event loop and logs the count.

## Files

| File | Note |
|---|---|
| `caliptra_ss_usb_hs_hub_int_ep_status_change.c` | MCU firmware: standard hub bring-up plus EP0 poll loop. Provides the DCON edge; never touches the hub EP1 IN endpoint, which is pure hardware. |
| `caliptra_ss_usb_hs_hub_int_ep_status_change.yml` | Test entry, `+UVM_TESTNAME=caliptra_ss_usb_hs_hub_int_ep_status_change_test` |
| `cptra_bringup.c` | symlink to `../libs/usb/bringup/cptra_bringup.c` |
| `.../uvm/usb/caliptra_ss_usb_hs_hub_int_ep_status_change_sequence.svh` | Host sequence |
| `.../uvm/usb/caliptra_ss_usb_hs_hub_int_ep_status_change_test.svh` | Test class: declares the hub INTERRUPT IN endpoint model |

## Debug history (MEASURED)

First simulation run: compiles and elaborates clean, hub enumeration completes,
and the status plane is confirmed - `GetPortStatus` returned `0x00010501` at
365866 ns, so `C_PORT_CONNECTION` (bit 16) is set as the test requires. The
first `INT_IN_EP1_connectChange` transfer was issued at 365866 ns and then did
**not** complete.

Two distinct testbench causes, both since fixed, plus one open RTL issue on the
idle leg. All three are recorded below.

**Fixed: the MCU halted mid-sequence.** `USB_POLL_TIMEOUT` was copied as 5000
from `caliptra_ss_usb_hs_hub_endpoint_halt`, which is EP0-only and finishes
early. Here 5000 polls bought only ~567 us of firmware life, so the MCU halted
at 567497 ns - and the MCU halt ends the simulation. The run therefore stopped
before the sequence could reach a verdict on any leg.

Simply enlarging the budget is not the fix: this firmware has no
work-completion condition of its own (the host addresses only the hub, so no
traffic ever reaches the MCU), so any constant is a guess that has to be
re-guessed whenever either side changes, and it silently converts a host-side
stall into a pass or a misattributed timeout.

The halt is now ordered by the host, using the MCU STOP handshake already in
use by `caliptra_ss_usb_fs_dev_lpm_l1_dev_wakeup` and the OCP-recovery tests -
no new mechanism:

| Side | What it does |
|---|---|
| Sequence, `request_mcu_stop()` (step 8 of `body()`) | `issue_mcu_command_bounded()` with opcode `0x7`, which holds the command on MCI `GENERIC_INPUT_WIRES_1` until the ack arrives, so polling firmware cannot miss it |
| Firmware, end of each poll iteration | Decodes magic + opcode, acks by echoing the command with `ACK_MAGIC` on `GENERIC_OUTPUT_WIRES_1`, then breaks and halts |

The opcode `0x7` appears in three places that must change together:
`MCU_STOP_OPCODE` in the sequence, `MCU_COMMAND_STOP` in
`caliptra_ss_usb_legacy_ep0_observer_if`, and `USB_LEGACY_EP0_COMMAND_STOP` in
`libs/usb/usb.h`.

Both halves are bounded and neither can fail the test on the other's account.
A missing ack is `uvm_info` on the host side, and `USB_POLL_TIMEOUT` (now
40000) remains purely as the firmware's safety ceiling for the case where the
STOP never arrives - an older sequence, an observer interface not wired into
the TB, or a host-side failure earlier in the run. That preserves the old
behaviour of halting on its own rather than hanging the simulation.

**OPEN RTL ISSUE: the idle leg is not NAKed on the first token.** With every
change bit acknowledged, and `GetPortStatus` returning `wPortChange = 0x0000`,
the hub still answers the first EP1 IN token with one byte of `0x00` instead of
NAKing.

Two mechanisms could explain a single answered token:

* (a) the endpoint draining one buffer that was already armed and loaded at the
  moment the change bits were cleared - the next token then NAKs
* (b) a permanently armed endpoint - every later token answered.

A two-token experiment was run to separate them, and measured **(a)**:

| Time | Event |
|---|---|
| 453811 ns | first idle IN token -> `DATA1`, 1 byte `0x00` |
| 454811 ns onward | second token |
| 455227 - 459410 ns | **9 x NAK** from the device |
| 459412 ns | second poll completes with no payload |

So the endpoint does de-arm after one token. **However, the designer confirmed
that this is still not the required behaviour: the NAK must happen on the FIRST
token once the change bits are cleared.** The two-poll leg was therefore
tolerating a real defect, and the leg has been reverted to a single poll that
fails if any payload comes back. The test is expected to fail on this leg until
the RTL is fixed.

A candidate location, offered as a lead rather than a conclusion:
`reg_ep_active(0)` in `usb_ep_config_handler.m.vhdl` is set-only on the hub's
hardware-armed path (line 256 assigns a literal `'1'`), its intended clear is
the unimplemented `-- TODO : Add code to clear active bit if it was still set !!`
at line 310, and that TODO's guard `ep_clear_buffer(0)` is tied off by
`hub_epin_clear_buffer <= '0'` (`usb_app_hw_hub.m.vhdl:436`, wired at
`structure:2414`). The measured 9 NAKs show something else does clear the arm
after one token, so this is not by itself the explanation.

**Fixed earlier: the EP1 IN transfer never terminated.** The SVT transcript
settled this and exonerates the DUT on this specific point - it says nothing
about the open idle-leg issue above. From
`env.host_agent.link_mon.20.*.pkt_trace`:

| Observation | Value |
|---|---|
| First `TOKEN IN addr 1 ep 1` | 365781.203 ns - only 50 ns after the sequence issued the transfer |
| Hub response | `DATA0` / `DATA1`, 1 byte, payload `0x02` - exactly the predicted bitmap with bit 1 set for port 1 |
| Data toggle | `DATA0` / `DATA1` alternating correctly |
| Host response | `HANDSHAKE ACK` after every packet |
| IN tokens to addr 1 ep 1 | 4307, still polling at 4118797 ns |
| Reported transfer status | `ACTIVE` (expected `ACCEPT`), `results_status = 0x0` |

So the hub arms, grants, and returns the right byte on the first token, and the
host accepts it - the gap-G1 signals are being exercised. What never happened was
the *VIP* declaring the transfer finished.

Cause: `max_packet_size` was declared 1 (copying the descriptor) **and**
`allow_aligned_transfer_without_zero_length` was set. A transfer ends on a short
packet or on a zero-length terminator, and that pair removes both - with a 1-byte
maximum no packet can ever be short, and the ZLP wait was explicitly waived. The
VIP had no criterion left and polled until the sequence timeout.

The flag was also wrong on its own terms. All 24 other uses in the repo are on
OUT endpoints, where it exists because the IP_3511/3516 firmware neither appends
nor consumes a ZLP after a max-packet-aligned OUT; it says nothing about an IN
read. `caliptra_ss_usb_hs_dev_int_loopback_test` is the precedent - it sets the
flag on its INTERRUPT OUT entry and leaves its INTERRUPT IN entry without it.

Fix: `HUB_INT_MAX_PKT = 64` and the flag removed. The sequence still asks for 1
byte, so the hub's single byte is now a short packet (1 < 64) and the transfer
completes on the first ACK by the ordinary USB rule. `max_packet_size` here is the
host VIP's model of the remote endpoint, not a DUT input and not compared against
the descriptor - the real `wMaxPacketSize = 0x0001` is checked independently off
EP0 by `caliptra_ss_usb_data_check_api_impl` - so no check is weakened. The legs
assert the bitmap *value*, never the packet geometry.

Two earlier hypotheses are **disproven** by the same transcript and should not be
revisited:

* *bInterval as an HS exponent (12 -> 256 ms) starved the schedule.* No - the
  first token arrived 50 ns after the transfer was issued.
* *`BUFF = 0` means the endpoint cannot complete a transfer*
  (`claude_md/22_usb_hub_endpoint_halt.md` section 7). No - the bufferless
  endpoint answers IN tokens correctly, with the right data and toggle.

Note also that `prot_mon.HS.xfer_trace` logs only *completed* transfers. An
unterminated transfer is absent from it, which is what made the tokens look like
they were never driven. Use `link_mon.*.pkt_trace` for packet-level truth.

## Notes for whoever picks this up

* The VIP endpoint model declares `max_packet_size = 64`, deliberately NOT the
  descriptor's `wMaxPacketSize = 0x0001`. This is the host's transfer
  granularity, and 64 is what makes the hub's single byte a short packet and so
  terminates the transfer. Declaring 1 hangs the transfer - see the debug history.
* `max_retry_due_to_nak` is cut to 8 on this endpoint only. The shared
  configuration raises it to 500 for software-polled MCU endpoints; the hub
  endpoint is pure hardware and answers immediately, so the large budget buys
  nothing and would cost 501 tokens on the deliberately-NAKed idle leg.
* The idle leg is placed **last** and can be disabled with `CHECK_NAK_LEG = 0`
  in the sequence, so neither its known failure nor any VIP transfer-level noise
  from the expected abort can mask the three bitmap legs.
* The idle leg polls EP1 IN **once** and fails on any payload. Do not relax this
  to "judge only the second of two polls": that revision existed, and it
  tolerated the open RTL issue described in the debug history.
* UVM output goes to `svt_debug.transcript`, not `vcs_sim.log`, when the SVT
  transcript is enabled: `vcs_sim.log` carries only the final summary and ~55 of
  the 55589 UVM_INFO lines. Use
  `grep -E "=== STEP|USB_HUB_INT_EP_SC" svt_debug.transcript` to follow the test.
  Also note `prot_mon.*.xfer_trace` logs only *completed* transfers - use
  `link_mon.*.pkt_trace` for packet-level truth.
* `wait_xfer_done()` is never called after `do_data_xfer()`: the latter already
  waits internally. See `claude_md/22_usb_hub_endpoint_halt.md` section 7 - that
  exact mistake hung the first attempt at an interrupt IN probe on this endpoint.
* The `.c` file's IDE errors (`incomplete type "enum printf_verbosity"`,
  `identifier "LOW" is undefined`) are include-path artefacts present in every
  USB test `.c` and must NOT be "fixed".

<!-- File contains AI-generated response based on internal company sources -->
