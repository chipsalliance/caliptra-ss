# Caliptra-SS USB Functional Coverage

Reference and tracking document for the USB functional coverage model.

- **Part 1** - how the coverage is collected and attached.
- **Part 2** - the covergroup inventory: every covergroup, coverpoint and
  cross currently implemented.
- **Part 3** - implementation notes worth knowing before changing anything.

Current state: **25 covergroup types / 39 instances**, all verified present
and recording in the coverage database.

---

## Part 1 - Collection architecture

### 1.1 File layout

```
src/usb/coverage/
  usb_cov_pkg.sv         shared enums and classifier functions
  usb_dev_link_cov.sv    area A      probe-fed, x DEV0/DEV1
  usb_dev_enum_cov.sv    area B      probe-fed, x DEV0/DEV1
  usb_dev_ep_cov.sv      areas C, D  probe-fed (PIE, dev-qualified), x DEV0/DEV1
  usb_hub_cov.sv         area E      probe-fed, HUB
  usb_compound_cov.sv    area F      probe-fed, COMPOUND
  usb_addr_cov.sv        area G      bind
  usb_power_cov.sv       area H      bind
  usb_cov_bind.sv        bind statements
src/integration/testbench/
  usb_cov_probe_caliptra_ss.sv   all hierarchy paths, all probe-fed instances
```

Build wiring: the observers are listed in
`src/integration/config/caliptra_ss_top_tb.vf` (package first, bind last) and
named in `tools/scripts/cov_usb.cfg` for `-cm_hier` scoping. Everything is
guarded by `USB_FCOV`, so a build without the define carries no coverage
instrumentation at all.

### 1.2 Two attachment mechanisms

The split is forced by the RTL, not chosen.

**`bind` by module type** (areas G, H). A `bind` resolves its port expressions
in the **target module's own scope**, so it reaches any identifier declared in
that module - ports, internal nets and localparams alike. Because it names a
module *type* and never a hierarchy path:

- the same file compiles unchanged into the subsystem bench
  (`caliptra_ss_top_tb`) and the compound unit bench (`usb_top_tb`);
- it attaches to every instance of the target automatically;
- the covergroup and bin names are identical in both benches, which is what
  lets URG merge the two databases with no manual mapping.

**Probe + XMR** (areas A-F). `bind` **cannot target a VHDL entity**, and the
compound IP is VHDL, so its internals are reachable only by absolute
cross-module reference from a bench-specific probe module. Constraints found
in practice and respected by the probe:

- only **ports of VHDL sub-instances** are reliably reachable; compound
  architecture signals generally are not;
- VHDL generics are rejected (`VHDLXMRE-NS`);
- instances inside **unnamed generate blocks** cannot be resolved (`XMRE`) -
  this is why `dma_ahb_selected` is re-derived in the probe rather than read
  from `usb_dma_1`.

The coverage models themselves stay free of hierarchy strings; all of them live
in the one bench-specific probe file, so the models remain portable and
mergeable.

### 1.3 Scope model

| Scope | Probe root (under `u_hub_compound.`) | Identified by |
|---|---|---|
| **DEV0** | `usb_reg_if_1` | instantiated with `C_DEV0_*` generics |
| **DEV1** | `usb_reg_if_2` | instantiated with `C_DEV1_*` generics |
| **HUB** | `usb_ep0_hub_descr_1`, `usb_app_hw_hub_1` | hub has no `usb_reg_if` of its own |
| **COMPOUND** | `usb_pie_1`, `usb_synchronizer_1`, decoder, wrapper | shared / arbitration level |

DEV0 and DEV1 instance the **identical** covergroup set (areas A-D): same
covergroup type, two instances, so bin names match and URG still merges while
the per-device numbers stay separately visible.

### 1.4 The PIE is shared - device attribution is mandatory

`usb_pie_1` is instantiated **exactly once** and is time-multiplexed across all
three functions (it is handed `C_NBDEV+2` = hub + dev0 + dev1) and exports
`pie_dev_selected`. Therefore:

- PIE-sourced signals are **COMPOUND** scope, not per-device;
- every PIE-sourced sample must be qualified by `pie_dev_selected`, which is
  how area C stays per-device. Without the qualifier area C would attribute
  dev1 traffic to dev0 - this is a correctness requirement, not a style choice;
- `usbreg_*` / `sync_*` signals on `usb_reg_if_1/_2` are genuinely per-device
  and need no qualifier.

`pie_dev_selected` is safe to use live. It is driven from the registered
`pie_dev_selected_int`, assigned in exactly one place - inside the
`new_inoutsetup_vld = '1'` branch of the token-decode process - so it **holds
for the whole transaction** and only changes when the next token selects a
different device. Area C additionally qualifies on a transaction-active window
(`epinfo_req` to `pie_endtransfer`) so the idle selection value of 0 is not
miscounted as dev0 traffic.

Device index numbering follows `usbreg_deviceenabled`: hub = 0, dev0 = 1,
dev1 = 2 (`USB_SEL_*` in `usb_cov_pkg.sv`).

### 1.5 Sampling conventions

- **Transitions, not levels**, wherever the question is "did this ever
  happen". A bit sampled high at an arbitrary time only proves the reset value;
  a `0=>1` edge proves the event occurred.
- **Every coverpoint is qualified by `iff (rst_n)`** at minimum, plus an
  event-specific qualifier where the sample is only meaningful in context.
- **Illegal combinations use normal bins named `illegal_*`**, not SystemVerilog
  `illegal_bins` (which kills the simulation) and not `ignore_bins` (which
  reports nothing). **A non-zero `illegal_*` bin is a failure signal, not a
  coverage hole.**
- Coverpoints are **local to their covergroup**, so each group needing a speed
  cross declares its own `cp_speed_*`.

### 1.6 Reporting

```bash
# text report
urg -dir usb_cov.vdb -report urg_out -format text

# interactive
verdi -cov -covdir usb_cov.vdb
```

---

## Part 2 - Covergroup inventory

### Area A - Link power state

Observer `usb_dev_link_cov.sv`, scope DEV0 + DEV1 (**3 types / 6 instances**).
Link state is decoded as
`link_state_e = {L0_ACTIVE, L1_SLEEP, L2_SUSPEND, DISCONNECTED}` from
`{usbreg_dev_connect, sync_suspend, sync_lpm_Suspend}`. L1 is checked before L2
because the IP shares `DSUS_C`.

| Covergroup | Coverpoints | Crosses |
|---|---|---|
| `usb_link_state_cg` | `cp_state`, `cp_transition` (enter/exit L1, enter/exit L2, connect, disconnect + `illegal_l1_to_l2`, `illegal_l2_to_l1`, `illegal_disc_to_l1`, `illegal_disc_to_l2`), `cp_speed` | `cross_state_speed`, `cross_transition_speed` |
| `usb_lpm_l1_cg` | `cp_l1_entry`, `cp_l1_exit_cause` (host-resume / device-wakeup / busreset), `cp_rewp`, `cp_nyet`, `cp_hird_sw`, `cp_hird_hw_match`, `cp_speed_l1` | `cross_exit_rewp`, `cross_l1_speed`, `cross_hird_entry` |
| `usb_l2_suspend_cg` | `cp_l2_entry`, `cp_l2_exit_cause` (host-resume / device-wakeup / busreset / vbus-loss), `cp_needclk_at_entry`, `cp_speed_l2` | `cross_exit_speed`, `cross_entry_needclk` |

Answers: which link states and legal transitions were reached and at which
speed; whether L1 is genuinely verified and how it was left; whether the HIRD
token round-tripped; whether L2 was ever entered with the clock still forced on.

### Area B - Enumeration and connection

Observer `usb_dev_enum_cov.sv`, scope DEV0 + DEV1 (**4 types / 8 instances**).

| Covergroup | Coverpoints | Crosses |
|---|---|---|
| `usb_enum_cg` | `cp_addr_assigned` (default / assigned + assign and clear edges), `cp_dev_en`, `cp_setup`, `cp_speed` | `cross_enum_speed` |
| `usb_connect_cg` | `cp_dcon` (connect / disconnect edges), `cp_vbus_debounced` | `cross_dcon_vbus` |
| `usb_reset_cg` | `cp_busreset`, `cp_reset_from_state`, `cp_addr_cleared`, `cp_speed_rst` | `cross_reset_state_speed` |
| `usb_speed_cg` | `cp_speed` (incl. `illegal_reserved`), `cp_force_fs`, `cp_xcvrselect`, `cp_termselect` | `cross_force_fs_speed`, `cross_speed_xcvr` |

Answers: did enumeration complete at both speeds; was connect ever asserted
without debounced VBUS; was a bus reset taken from each link state and did it
clear the address per spec; did forcing FS actually produce an FS link.

### Area C - Endpoint and transfer activity

Observer `usb_dev_ep_cov.sv`, scope DEV0 + DEV1 (**4 types / 8 instances**).
All PIE-sourced, so **every coverpoint is qualified by
`pie_dev_selected == MY_SEL` plus a transaction-active window** (see 1.4).

| Covergroup | Coverpoints | Crosses |
|---|---|---|
| `usb_ep_activity_cg` | `cp_ep_num` (0-15), `cp_dir`, `cp_ep_kind` (control / iso / bulk-int) | `cross_ep_dir`, `cross_kind_dir` |
| `usb_transfer_outcome_cg` | `cp_outcome` (success / NAK / error), `cp_errortype` (0-15), `cp_stall`, `cp_ep_num_out`, `cp_kind_out` | `cross_outcome_ep`, `cross_errtype_kind` |
| `usb_transfer_size_cg` | `cp_size` (ZLP / 1 / small / 64 / 65-511 / 512 / 513-1022 / 1023 / 1024 / >1024), `cp_kind_sz`, `cp_dir_sz` | `cross_size_kind`, `cross_size_dir` |
| `usb_ep_buffer_cg` | `cp_toggle`, `cp_bufinuse`, `cp_skip`, `cp_disabled`, `cp_inactive` | `cross_toggle_bufinuse` |

Answers: which endpoints were exercised in which direction and of which kind;
did every endpoint see a success and which error classes occurred; were the ZLP
and max-packet boundary cases hit; was double-buffering exercised with the
toggle tracking it, and was the skip path used.

### Area D - Interrupts

In `usb_dev_ep_cov.sv`, scope DEV0 + DEV1 (**1 type / 2 instances**).

| Covergroup | Coverpoints | Crosses |
|---|---|---|
| `usb_interrupt_cg` | `cp_irq` (assert + deassert), `cp_state` | `cross_irq_state` |

FIQ is not connected in this design - every source routes to IRQ - so the FIQ
coverpoint was removed rather than carried as a permanent hole.

Answers: did each device raise IRQ, and was an interrupt ever raised
while the link was in a low-power state. Both edges matter: the rising edge
proves the subsystem generated a request, the falling edge proves firmware
could clear the underlying status.

### Area E - Hub

Observer `usb_hub_cov.sv`, scope HUB (**6 types / 8 instances**;
`usb_hub_port_cg` is instanced per port).

| Covergroup | Coverpoints | Crosses |
|---|---|---|
| `usb_hub_config_cg` | `cp_hub_enable`, `cp_hub_dcon`, `cp_vbus_debounced`, `cp_force_vbus`, `cp_lpm_sup`, `cp_force_fs`, `cp_pll_on`, `cp_self_powered`, `cp_speed`, `cp_phy_test_mode` | `cross_dcon_vbus`, `cross_force_fs_speed`, `cross_mode_speed` |
| `usb_hub_write_lock_cg` | `cp_outcome` (accepted-unlocked / blocked-locked / exempt-locked / dropped-out-of-range), `cp_word_class` | `cross_outcome_word_class` |
| `usb_hub_port_cg` (per port) | `cp_connect`, `cp_enable`, `cp_suspend`, `cp_reset`, `cp_l1`, `cp_connect_level`, `cp_enable_level` | `cross_connect_enable`, `cross_suspend_enable` |
| `usb_hub_port_independence_cg` | `cp_connect_pattern` (incl. per-port cycle sequences), `cp_enable_pattern` | - |
| `usb_hub_status_change_cg` | `cp_change_reported`, `cp_epin_stall`, `cp_epin_enable_buffer` | `cross_stall_armed` |
| `usb_hub_class_req_cg` | `cp_request`, `cp_recipient` (hub / port1 / port2 / out-of-range), `cp_feature`, `cp_stall` | `cross_request_recipient`, `cross_feature_stall` |
| `usb_hub_remote_wakeup_cg` | `cp_outcome` (granted / dropped-not-suspended / dropped-wake-disabled / dropped-port-disabled), `cp_wake_enabled`, `cp_suspended`, `cp_wake_enable_cleared`, `cp_busreset` | `cross_gate_terms` |

Answers: which hub configurations were ever run; whether the descriptor
write-lock rule holds in each state including the three lock-exempt registers;
whether each downstream port reached connect/enable/suspend/reset/L1 and
reported its changes; whether the ports were ever independently up and down;
which class requests were dispatched and which were stalled; and why a
device-initiated wakeup was granted or silently dropped.

### Area F - Compound multiplexing

Observer `usb_compound_cov.sv`, scope COMPOUND (**2 types / 2 instances**).

| Covergroup | Coverpoints | Crosses |
|---|---|---|
| `usb_compound_function_cg` | `cp_function` (hub / dev0 / dev1), `cp_dma_context`, `cp_function_interleave` (all six directed switches), `cp_enabled_legs`, `cp_hub_enable` | `cross_function_dma`, `cross_mode_enabled_legs` |
| `usb_compound_concurrency_cg` | `cp_dev0_state`, `cp_dev1_state`, `cp_both_enumerated` | `cross_dev_states` |

Answers: was the shared serial engine genuinely handed to all three functions
and did it interleave between them rather than serving one for the whole run;
did the DMA context follow into both ranges; and - the headline question that
only per-device instancing enables - were dev0 and dev1 ever in *different*
link power states at the same time.

### Area G - Address map and access semantics

Observer `usb_addr_cov.sv`, **bind** to `usb_compound_ahb_decoder`
(**2 types / 2 instances**).

| Covergroup | Coverpoints | Crosses |
|---|---|---|
| `usb_combo_access_cg` | address phase: `cp_region`, `cp_dir`, `cp_shape`, `cp_select`; data phase: `cp_resp`, `cp_resp_region`, `cp_resp_dir`, `cp_error_phase` | `cross_region_dir`, `cross_region_shape`, `cross_region_dir_resp` |
| `usb_hub_word_access_cg` | `cp_word_class`, `cp_dir` | `cross_word_class_dir` |

Answers: was every architecturally distinct sub-region accessed in both
directions; did each region return its architected response class (the decode
hole an ERROR, the hub aperture padding an OKAY); were non-32-bit and unaligned
accesses attempted and did they correctly select no responder; and which hub
word classes were reached.

The address-phase and data-phase coverpoints are deliberately named apart
(`cp_region` vs `cp_resp_region`) so a cross can never pair an address-phase
term with a data-phase one, which would compare two different transfers.

### Area H - Clock, reset context and OCP claim

Observer `usb_power_cov.sv`, **bind** to
`ip_xxx_3511_hs_mem_compound_wrapper` (**3 types / 3 instances**).

| Covergroup | Coverpoints | Crosses |
|---|---|---|
| `usb_clock_request_cg` | `cp_needclk` (request + release edges), `cp_suspended` | `cross_needclk_suspend` |
| `usb_reset_context_cg` | `cp_utmi_reset`, `cp_context_vbus`, `cp_context_busy` | `cross_reset_context` |
| `usb_ocp_claim_cg` | `cp_payload_available`, `cp_firmware_activated` | - |

Answers: was the clock request ever **released**, or does it stay asserted for
the whole run because FORCE_NEEDCLK masks it permanently - and was the release
taken while suspended, where it matters; was a reset ever taken while the
subsystem was busy rather than idle; did the OCP recovery claim handshake
complete.

This observer is deliberately small. Interrupt delivery, suspend/resume and
topology coverage live in the per-device and hub/compound observers instead,
because the wrapper ports visible here are the *merged* subsystem view and
cannot be attributed to a device. What remains is what is genuinely singular
for the whole compound: one clock request, one UTMI reset.

### Summary

| Area | Observer | Scope | Types | Instances |
|---|---|---|---|---|
| A - link power | `usb_dev_link_cov` | DEV0, DEV1 | 3 | 6 |
| B - enumeration | `usb_dev_enum_cov` | DEV0, DEV1 | 4 | 8 |
| C - endpoints / transfers | `usb_dev_ep_cov` | DEV0, DEV1 | 4 | 8 |
| D - interrupts | `usb_dev_ep_cov` | DEV0, DEV1 | 1 | 2 |
| E - hub | `usb_hub_cov` | HUB | 6 | 8 |
| F - compound | `usb_compound_cov` | COMPOUND | 2 | 2 |
| G - address map | `usb_addr_cov` | COMPOUND (bind) | 2 | 2 |
| H - clock / power | `usb_power_cov` | COMPOUND (bind) | 3 | 3 |
| **Total** | | | **25** | **39** |

---

## Part 3 - Implementation notes

Things that are not obvious from the code and are easy to get wrong when
extending the model.

### 3.1 Transfer-size buckets are absolute, not max-packet relative

`usb_transfer_size_cg` cannot bucket against the endpoint's actual max-packet
size. The real limit is derived inside `usb_dma` from speed +
`epinfo_periodic` + `epinfo_rf_tv` + endpoint number (see CHECK_EPINFO in
`usb_dma.m.vhdl`), and `usb_dma_1` sits in an unnamed generate block, which
VCS refuses to resolve by cross-module reference. `epinfo_maxpacket[1:0]` alone
does not encode the limit.

`xfer_size_class()` therefore buckets on the **absolute architectural
boundaries** that apply across all configurations, so the 64 / 512 / 1023 /
1024 packet-size edges each get their own bin whichever configuration is live.

### 3.2 Port-vector properties stay out of the per-port group

`usb_hub_port_cg` is instanced **per port inside a generate loop**. A
whole-vector coverpoint placed there would be duplicated once per port with
both copies measuring the same thing. Port independence is a property of the
port *vector*, so it lives in its own `usb_hub_port_independence_cg`, sampled
once.

### 3.3 Unreachable signals and the substitutions used

| Wanted | Problem | What is probed instead |
|---|---|---|
| `dma_ahb_selected` | `usb_dma_1` is in an unnamed generate block | re-derived in the probe as `pie_dev_selected >= C_NBDEV`, reproducing the compound's own expression |
| compound `pie_dev_selected` | VHDL integer, awkward to bridge | `usb_ocp_recovery_post_sync_arb_1.pie_dev_selected_i`, the same selection as a 2-bit vector |
| compound `hub_remotewakeup` | architecture signal, no port | `usb_pie_1.usbreg_remotewakeup`, which carries it unchanged in hub mode |
| INTONNAK enables (DEVCMDSTAT 12-15) | not exposed as `usb_reg_if` ports | not covered; the observable consequence is `usb_transfer_outcome_cg.cp_outcome` |
| hub PHY test mode | hub has no `usb_reg_if` | DEV0's `usbreg_phy_test_mode`; the PHY is shared compound-wide |

Each substitution is also commented at its point of use in the probe.

### 3.4 Hub-port L1 and device L1 are separate mechanisms

Hub-port L1 (`usb_hub_port_cg.cp_l1`) and device L1 (`usb_lpm_l1_cg`) are
deliberately *not* merged. One is a downstream port facing a device, the other
is the device's own link. Combining them behind a scope coverpoint would
cross-contaminate the L1 exit-cause bins, which are device-specific. The two
groups together cover the `dual_device_*_hub_port_l1` tests from both ends.
