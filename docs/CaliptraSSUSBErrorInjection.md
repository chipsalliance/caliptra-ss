# Caliptra SS USB error-injection test family

This document is the single reference for the nine `caliptra_ss_usb_hs_dev_err_*`
test suites. The per-suite `README.md` files are deliberately thin and point
here, because the interesting content - the RTL derivation of the error codes
and the VIP field model - is shared.

## 1. What these tests are stimulus for

`usb_transfer_outcome_cg.cp_errortype` in
`src/usb/coverage/usb_dev_ep_cov.sv`. That coverpoint samples the PIE's
`pie_errortype` output at end of transfer whenever `pie_error` is set:

```systemverilog
cp_errortype: coverpoint xfer_errortype iff (xfer_done_for_me && xfer_error) { ... }
```

Before this work only two of its bins were ever hit:

| code | name | status before |
|---|---|---|
| 0x6 | `timeout` | already covered |
| 0x9 | `sent_received_nak` | already covered |

Everything else sat at zero on both `dev0` and `dev1`, because nothing in the
regression ever produced a protocol error. The nine tests below close the rest.

### A correction to the original task framing

The task this work came from asked to close coverage "area G". Area G is the
**AHB address map and access semantics** (`usb_addr_cov.sv`,
`usb_combo_access_cg`, bound to `usb_compound_ahb_decoder`) - see
`CaliptraSSUSBCoveragePlan.md` section "Area G". It contains no error-injection
bins at all. The real error-injection gap is in area C, `cp_errortype`, which is
what these tests target.

## 2. The error-code legend is RTL-derived

`pie_errortype` is 4 bits wide and its encoding appears in **no specification**.
It comes from the `SetError` procedure of
`third_party/usb2/src/usb_hub_composite_device/RTL/RTL/usb_pie.m.vhdl`. That
procedure was commented out by a lint fix and its body inlined at every call
site ("Removed procedure and moved code explicitly in design to fix lint
error"), so:

- the surviving comment block at **lines 1901-1918** is the legend;
- the live `errortype <= "...."` assignments are the authority for what the
  design can actually still produce.

Measured live-site counts:

| code | name | live sites | reachable | test |
|---|---|---|---|---|
| 0x0 | `ERROR_NO_ERROR` | reset only | no | - |
| 0x1 | `ERROR_PID_ENCODING` | 4 | yes | `..._err_pid_check` |
| 0x2 | `ERROR_PID_UNKNOWN` | 9 | yes | `..._err_pid_illegal` |
| 0x3 | `ERROR_PACKET_UNEXPECTED` | 7 | yes, ISO only | `..._err_pkt_unexpected` |
| 0x4 | `ERROR_TOKEN_CRC` | 2 | yes | `..._err_token_crc` |
| 0x5 | `ERROR_DATA_CRC` | 1 | yes | `..._err_data_crc` |
| 0x6 | `ERROR_TIMEOUT` | 5 | already covered | - |
| 0x7 | `ERROR_BABBLE` | **0** | **no** | removed from collection |
| 0x8 | `ERROR_TR_EOP` | 4 | yes | `..._err_short_pkt` |
| 0x9 | `ERROR_SENT_RECEIVED_NAK` | 4 | already covered | - |
| 0xA | `ERROR_SENT_STALL` | 3 | yes | `..._err_stall` |
| 0xB | `ERROR_OVERRUN` | 2 | yes | `..._err_long_pkt` |
| 0xC | `ERROR_SENT_EMPTYPACK` | **0** | **no** | removed from collection |
| 0xD | `ERROR_BITSTUFF_ERROR` | **0** | **no** | removed from collection |
| 0xE | `ERROR_SYNC_ERROR` | **0** | **no** | removed from collection |
| 0xF | `ERROR_DATA_IGNORED_WRONG_DATA01` | 1 | yes | `..._err_toggle` |

### Bins removed rather than waived

0x7, 0xC, 0xD and 0xE have **no live assignment anywhere** in `usb_pie`: the
only occurrence of each is inside the dead commented-out procedure. They are
unreachable by any stimulus whatsoever, so per review direction they were
**removed from the coverpoint** rather than chased or waived. 0x0 is excluded
for a different reason: the coverpoint is qualified
`iff (xfer_done_for_me && xfer_error)`, so the no-error code can never coincide
with a sample.

Note in particular that **0xD and 0xE are the bit-stuffing and SYNC codes**.
Injecting `svt_usb_packet_exception` `BIT_STUFF_ERROR` or `SYNC_ERROR` does
corrupt the wire, but this PIE never reports either through `pie_errortype`, so
those injections cannot close a bin and are deliberately not used.

## 3. The SVT VIP exception field model

Verified against the generated class reference at
`/pkg/synopsys-designware-/vip_collection/vip/svt/usb_svt/latest/doc/class_ref/usb_svt_uvm_class_reference/html/exception/`
and against the three in-repo sequences that already used the framework
(`caliptra_ss_usb_ocp_packet_observer_selftest_sequence`,
`caliptra_ss_usb_ocp_stall_base_sequence`,
`caliptra_ss_usb_ocp_directed_packet_sequence`).

`error_kind` **is** the top-level selector in all four exception classes, and it
enables exactly one sub-field:

| `error_kind` | enabled sub-field |
|---|---|
| `CRC_ERROR` | `crc_error` (`CRC5_ERROR`, `CRC16_ERROR`, ...) |
| `PHYSICAL_ERROR` | `physical_error` (`SYNC_ERROR`, `EOP_ERROR`, `BIT_STUFF_ERROR`, `BYTE_BOUNDARY_ERROR`, `PRE_PID_ERROR`, `RX_ERROR`) |
| `LENGTH_ERROR` | `length_error` (`SHORT_PACKET_ERROR`, `LONG_PACKET_ERROR`, ...) |
| `FRAMING_ERROR` | `framing_error` (SuperSpeed only) |
| `DATA_ERROR` | `data_error` (SuperSpeed only) |
| `PACKET_FIELD_ERROR` / `RESERVED_FIELD_ERROR` | `field_id`, with `mask_or_value` carrying the replacement value |

`PID_CHECK_ERROR` and `ILLEGAL_DATA_PID_ERROR` are standalone `error_kind`
values needing no sub-field.

Consequences worth stating explicitly:

- `SYNC_ERROR`, `EOP_ERROR`, `BIT_STUFF_ERROR`, `BYTE_BOUNDARY_ERROR` and
  `RX_ERROR` are **not** `error_kind` values. They are `physical_error_enum`
  members, reachable only with `error_kind == PHYSICAL_ERROR`.
- `RX_ERROR` is documented as "only for reporting purpose" and cannot be
  injected at all.
- `mask_or_value == 0` is explicitly invalid for `CRC_ERROR`, because the mask
  is XORed with the CRC field and 0 would leave it correct.

### `error_kind` legality depends on the packet type

The table above says which sub-field an `error_kind` enables; it does not say
which `error_kind` values are legal in the first place. That comes from the
VIP's own `valid_ranges` constraint, read out of
`sverilog/src/com/svt_usb_packet_exception.svp:3163`:

```
if (xact.pid_type == svt_usb_packet::DATA)
  error_kind inside {CRC_ERROR, PHYSICAL_ERROR, ILLEGAL_DATA_PID_ERROR,
                     PID_CHECK_ERROR, LENGTH_ERROR, NO_OP_ERROR};
else if (HANDSHAKE, or SPECIAL with PRE_ERR)
  error_kind inside {PHYSICAL_ERROR, PACKET_FIELD_ERROR, PID_CHECK_ERROR,
                     NO_OP_ERROR};
else   // TOKEN, SPECIAL/PING, EXT_TOKEN
  error_kind inside {CRC_ERROR, PHYSICAL_ERROR, PACKET_FIELD_ERROR,
                     PID_CHECK_ERROR, NO_OP_ERROR};
```

Consequences this family depends on:

- `PACKET_FIELD_ERROR` is **illegal on a DATA packet**. Pinning it there is an
  unsatisfiable constraint and the solver fails - it is not a silent no-op.
  This is why `err_toggle` injects no exception at all; see section 5.
- `LENGTH_ERROR` is legal **only** on a DATA packet.
- `CRC_ERROR` and `PID_CHECK_ERROR` are legal on both DATA and TOKEN, which is
  what makes the CRC5-on-OUT-token and PID-check-on-OUT-token injections valid.
- The same block adds `xact.payload.byte_count == 0 -> error_kind != CRC_ERROR`,
  so a CRC injection needs a non-empty payload.

### `byte_offset` must be pinned for a length error

`byte_offset` carries how many bytes a `LENGTH_ERROR` adds or removes, and
`valid_ranges` only bounds it as `>= 0`. An unpinned solve may legally choose
0, leaving the packet correctly sized and injecting nothing - the test would
pass while covering nothing. `inject_error_packet()` therefore takes an
explicit `len_byte_offset`.

Two idioms taken verbatim from the working in-repo code and kept:

- `no_exception == 0` - without it randomization is free to decide that no
  error is injected after all.
- `recognized = 0`, assigned **after** `randomize()` - marks the exception as
  generated by us rather than recognised in a received packet.

Plus the null-guard before allocating `exception_list`, from the same source:
the list is shared per transaction and may already exist.

## 4. Why some tests inject nothing

Two of the nine bins are **not reachable by wire corruption at all**, because
their RTL guards read endpoint state that only firmware can set.

### `sent_stall` (0xA)

All three live sites are guarded by:

```vhdl
elsif epinfo_stall = '1' and epinfo_active = '0' then -- stall handshake must be returned
   errortype <= "1010"; --ERROR_SENT_STALL
```

and `usb_dma.m.vhdl` lines 303 / 297 latch those straight out of the endpoint
command/status list entry:

```vhdl
epinfo_active <= dma_rdata(31);   -- USB_EP_ENTRY_ACTIVE
epinfo_stall  <= dma_rdata(29);   -- USB_EP_ENTRY_STALL
```

So the condition is literally "STALL set, ACTIVE clear" in the descriptor the
MCU firmware writes. The firmware is the stimulus; the sequence only supplies a
transaction to be stalled.

**Why the existing hub STALL test does not cover this bin.**
`caliptra_ss_usb_hs_hub_class_req_stall` does make a device STALL a control
request - but against the **hub**, at `HUB_ADDR = 1` with recipient
`BMREQ_OTHER`. The PIE is instantiated once and time-multiplexed, and
`usb_cov_probe_caliptra_ss.sv` instantiates `usb_dev_ep_cov` for `dev0` and
`dev1` **only**; there is no hub instance. A hub STALL is therefore never
sampled by this coverpoint, and a device-level STALL test is required.

### `packet_unexpected` (0x3)

Every one of its seven live sites is gated on an outstanding **isochronous**
transaction:

| line | condition |
|---|---|
| 2192 | `PID_IN` while `iso_out_pending_r = '1'` |
| 2211 | `PID_OUT` while `iso_in_pending_r = '1'` |
| 2231 | `PID_SETUP` while either iso flag set |
| 2251 | `PID_PING` while either iso flag set |
| 2295 | `PID_SOF` while either iso flag set |
| 2837 | iso OUT data packet to a STALLed endpoint |
| 2879 | iso OUT data packet to an endpoint with ACTIVE clear |

The iso pending flags are set only under `if epinfo_iso = '1'` (line 2500), and
`epinfo_iso` comes from the endpoint type bits of the list entry. On a bulk
endpoint both flags stay low and all five token-mismatch branches are dead - a
bulk sequencing error cannot reach this bin.

The test targets **line 2879**, the only site that is deterministic from the
host side alone: the five token-mismatch branches need a token inside the
window where a previous iso transaction is still pending, which races the SOF
boundary and the DMA handler, and 2837 needs the endpoint STALLed, which the
`sent_stall` test already covers.

## 5. The nine suites

| suite | bin | mechanism |
|---|---|---|
| `caliptra_ss_usb_hs_dev_err_data_crc` | `data_crc` 0x5 | `CRC_ERROR` / `CRC16_ERROR` on a bulk OUT |
| `caliptra_ss_usb_hs_dev_err_token_crc` | `token_crc` 0x4 | `CRC_ERROR` / `CRC5_ERROR` |
| `caliptra_ss_usb_hs_dev_err_pid_check` | `pid_encoding` 0x1 | `PID_CHECK_ERROR` |
| `caliptra_ss_usb_hs_dev_err_pid_illegal` | `pid_unknown` 0x2 | `ILLEGAL_DATA_PID_ERROR` |
| `caliptra_ss_usb_hs_dev_err_short_pkt` | `tr_eop` 0x8 | `LENGTH_ERROR` / `SHORT_PACKET_ERROR` |
| `caliptra_ss_usb_hs_dev_err_long_pkt` | `overrun` 0xB | `LENGTH_ERROR` / `LONG_PACKET_ERROR` |
| `caliptra_ss_usb_hs_dev_err_toggle` | `wrong_data_toggle` 0xF | a clean `DATA1` packet, no exception (`attach_exception == 0`) |
| `caliptra_ss_usb_hs_dev_err_stall` | `sent_stall` 0xA | firmware arms EP1 with STALL set, ACTIVE clear |
| `caliptra_ss_usb_hs_dev_err_pkt_unexpected` | `packet_unexpected` 0x3 | firmware arms ISO EP2 once, never re-arms |

All nine run at the **subsystem level** on USBDC0 at High Speed. There is no
block-level variant: both levels instantiate the same SVT VIP, so a second copy
would add run time without adding coverage.

## 6. File map

Testbench (all `include`d from `caliptra_ss_usb_test_pkg.sv`, so none of them
needs a `caliptra_ss_top_tb.vf` entry):

```
src/integration/testbench/uvm/usb/
  caliptra_ss_usb_err_inject_base_sequence.svh        shared helpers + the legend
  caliptra_ss_usb_hs_dev_err_crc_sequence.svh         crc_target selector
  caliptra_ss_usb_hs_dev_err_pid_sequence.svh         pid_error_kind selector
  caliptra_ss_usb_hs_dev_err_length_sequence.svh      length_target selector
  caliptra_ss_usb_hs_dev_err_sequence_sequence.svh    toggle skew
  caliptra_ss_usb_hs_dev_err_stall_sequence.svh       no injection
  caliptra_ss_usb_hs_dev_err_pkt_unexpected_sequence.svh  no injection, ISO
  caliptra_ss_usb_hs_dev_err_*_test.svh               nine test classes
```

Firmware:

```
src/integration/test_suites/libs/usb/usb_err_inject_fw_common.h
    shared body for the seven corruption suites
src/integration/test_suites/caliptra_ss_usb_hs_dev_err_stall/*.c
src/integration/test_suites/caliptra_ss_usb_hs_dev_err_pkt_unexpected/*.c
    bespoke, because for these two the firmware IS the stimulus
```

`usb_err_inject_fw_common.h` sits directly in `libs/usb/` and not in a
subdirectory because `tools/scripts/Makefile` builds with only
`-I$(BUILD_DIR)` and populates it from
`$(foreach comp_lib, $(COMP_LIBS), $(wildcard $(comp_lib)/*.h))` - a one-level
glob.

## 7. Where the exception attaches, and why

A `svt_usb_packet_exception` attaches to a `svt_usb_packet`, **never** to a
`svt_usb_transfer`. Two independent reasons:

1. **Wrong container.** `svt_usb_transfer.exception_list` is declared as a
   `svt_usb_transfer_exception_list`, which holds `svt_usb_transfer_exception`
   objects - a different class with a different error model
   (`payload_corrupted_error`, `invalid_packet_error`,
   `control_transfer_format_error`, `error_val`). It has no `crc_error`,
   `physical_error`, `length_error` or `field_id` member at all, so none of the
   wire corruptions this family needs can be expressed there.
2. **Unpopulated back-references.** `svt_usb_packet_exception` requires both
   `cfg` and `xact` to be populated, with `xact` being a `svt_usb_packet`;
   `inject()` dereferences `xact`. An earlier transfer-level version left it
   null and crashed inside the VIP with a null object access at
   `svt_usb_packet_exception.svp:9846`.

The corrupted stimulus is therefore driven one packet at a time by
`caliptra_ss_usb_err_inject_packet_sequence`, started on
`p_sequencer.usb_20_pkt_sequencer`. Two pre-existing in-repo users of the
framework do the same - `caliptra_ss_usb_ocp_directed_packet_sequence.svh` and
`src/usb/tb/sequences/usb_bad_pid_packet_seq.svh`.

This is also valid stimulus rather than a shortcut: `cp_errortype` samples what
the PIE reports about a packet it **received**, and the PIE cannot tell whether
a malformed OUT token or DATA packet came from a full host transfer or from a
single directed packet. Driving it directly is in fact more deterministic,
because exactly one packet reaches the DUT and exactly one `errortype` can
result.

The `start()` is bounded by a 200 us fork/join_any guard, because a malformed
packet may never be answered - a bad-CRC data packet gets no handshake at all,
so an unbounded `start()` could hang the test.

## 8. What a passing run looks like

The corrupted transfer is **expected to fail at the bus level** and no status
check is run on it. For example `usb_pie.m.vhdl` line 2950 says of a bad data
CRC: "BAD CRC: Data Packet Corrupted, no hanshake is returned" - the device
returns nothing at all, so the VIP reports the transfer as ABORTED or times
out. That is correct device behaviour per USB 2.0 section 8.7.1, not a test
failure.

The evidence that an injection worked is:

1. the coverage bin closing, and
2. the **clean transfer afterwards** succeeding, which proves the endpoint
   recovered rather than wedging.

The second point is the more important one. An error-injection test that only
injects tells you the error was detected, not that the device survived it. The
`sent_stall` test is the one exception: a functional stall persists until the
host clears it (USB 2.0 section 8.4.5), so that endpoint is left halted on
purpose and has no recovery leg.

### One VIP check is suppressed, in `err_toggle` only

Eight of the nine suites pass with every VIP check left strict. Their
corruptions go unanswered on the wire, but the VIP does not object, so nothing
needs relaxing.

`err_toggle` is different. Its stimulus is a well formed DATA1 sent out of
turn, and a device receiving a data packet with the wrong toggle must discard
it and return **no handshake** (USB 2.0 section 8.6.3) - which is exactly the
behaviour `pie_errortype = 0xF` reports. The VIP link layer cannot know the
packet was deliberately out of turn, so it starts its End-to-end Signal Delay
timer on the DATA1 and raises `tend_to_end_delay_check` when nothing answers.
That makes the test unpassable by construction, so the test sets that one check
to `svt_err_check_stats::EXPECTED` in `end_of_elaboration_phase`.

The suppression is scoped to that single check in that single test. Full
rationale, the failing timestamps, and the note that SVT checks cannot be
suppressed through `set_report_severity_id_override()` are in
`src/integration/test_suites/caliptra_ss_usb_hs_dev_err_toggle/README.md`.

## 9. Why every sequence ends with the MCU STOP handshake

None of these firmware images has a completion condition of its own. A corrupted
packet is *meant* to be discarded, so "the transfer finished" never happens on
the injection leg; the halted-endpoint and un-armed-ISO-endpoint tests are the
same by construction. The firmware therefore polled to a fixed ceiling
(`USB_ERR_POLL_TIMEOUT` / `USB_POLL_TIMEOUT`, 60000 iterations) and halted only
when that budget ran out.

The cost showed up as soon as the family was run as a regression: all seven
passing tests landed inside a **1 us spread** of each other at ~7.7 ms of
simulation, regardless of which error they injected, while the sequences' own
explicit delays (`LINK_SETTLE` 20 us + `ENUM_SETTLE` 10 us + `ERROR_SETTLE`
50 us + up to `INJECT_RESPONSE_BOUND` 200 us) account for under 300 us. The
simtime was set by the loop count, not by the stimulus.

Each sequence body now ends with `request_mcu_stop()`, which reuses the existing
MCI generic-wire command channel from the OCP-recovery work - the same mechanism
`caliptra_ss_usb_fs_dev_lpm_l1_dev_wakeup` and
`caliptra_ss_usb_hs_hub_int_ep_status_change` already use:

```
host_mcu_command -> GENERIC_INPUT_WIRES_1 -> firmware polls it
firmware acks via GENERIC_OUTPUT_WIRES_1 -> fw_snapshot_header
```

`issue_mcu_command_bounded()` holds the command asserted until the ack arrives,
so polling firmware cannot miss a pulse. Two deliberate non-failure properties:

- The firmware keeps its poll ceiling as a **fallback**, so a sequence without
  the handshake, or a testbench with no observer interface wired, behaves
  exactly as before rather than hanging.
- A missing ack is reported as `uvm_info`, not `uvm_error`, so this teardown
  step cannot fail a test whose actual checks all passed. The base test's
  MCU-halt monitor still applies.

The STOP check sits at the END of each poll iteration, so the iteration that
observes it has already serviced EP0 one last time.

The STOP opcode is `4'h7` and must stay in step across three places:
`MCU_STOP_OPCODE` in `caliptra_ss_usb_err_inject_base_sequence.svh`,
`MCU_COMMAND_STOP` in `caliptra_ss_usb_legacy_ep0_observer_if.sv`, and
`USB_LEGACY_EP0_COMMAND_STOP` in `libs/usb/usb.h`.

<!-- File contains AI-generated response based on internal company sources -->

