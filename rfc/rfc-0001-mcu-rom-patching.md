# [RFC-0001] MCU ROM Patching via PMP Trap-and-Patch

|              |                                                    |
|--------------|----------------------------------------------------|
| **Author** | Robert Schilling |
| **Contributors** | David Schrammel, Samuel Ortiz, Ravi Sahita |
| **RFC** | RFC-0001 |
| **Related** | [caliptra-sw#3399](https://github.com/chipsalliance/caliptra-sw/issues/3399) |

## Abstract

MCU ROM is immutable mask ROM with no hardware ROM patching mechanism.
This RFC proposes authenticated software ROM patching using the VeeR
EL2's existing PMP hardware. Patches stored in OTP fuses are verified
with Ed25519 signatures and dispatched via PMP instruction access faults
to replacement code in SRAM. The mechanism requires no RTL changes, no
new hardware blocks, and no modifications to the memory subsystem.

## Problem Statement

MCU ROM is fixed at tapeout and may contain vendor-specific code: PLL
initialization, fabric and IO controller configuration, GPIO setup, and
the streaming boot protocol. A post-silicon bug in any of these requires a
fix mechanism. Mutable firmware loaded from flash is not affected — it
can be updated in the field — but ROM code cannot.

## Design Summary

- ROM verifies OTP patch slots with Ed25519 before mutable firmware
  runs.
- Verified replacement code is copied to SRAM, synchronized with
  `fence.i`, and dispatched through PMP instruction faults on `NA4`
  no-execute ROM entries.
- Patch PMP state and SRAM reservations are live only during initial ROM
  boot and are cleared by `BOOT_RST_MCU` before mutable firmware starts.
- For each target address, the highest-numbered non-empty OTP slot is
  authoritative; earlier same-target slots are ignored.
- Patch failures are non-fatal by default for survivability. `CRITICAL`
  patches fail closed after their slot headers are readable.

## Alternatives Considered

### Hardware ROM Patch Controller

Dedicated logic can remap ROM fetches to overlay RAM when the PC matches
a patch table entry, as OpenTitan does. This is the conventional ROM
patching design, but Caliptra SS does not have this hardware. Adding it
would modify the MCU AXI instruction fetch path (`mcu_ifu_m_axi_if`) and
require new RTL verification, area, and timing closure.

### Software Hook Points (Jump Tables)

ROM could branch through SRAM jump tables at predetermined hook points.
This avoids RTL changes, but hook points must be chosen before tapeout,
add overhead and abstraction to ROM code, and cannot patch arbitrary
locations discovered later.

### PMP Trap-and-Patch (This Proposal)

Reuses VeeR EL2 PMP entries to trap execution at target ROM addresses
and redirect to authenticated replacement code in SRAM.

This proposal is selected because:
- **No RTL changes.** PMP is existing hardware. No additional
  verification, area, or timing impact.
- **Zero overhead on unpatched paths.** PMP checks are part of normal
  instruction fetch; unpatched code runs at full speed.
- **Natural ROM code.** No indirect branches, hook points, or patching
  abstractions baked into ROM source.
- **Arbitrary patch targets.** Can patch any 4-byte-aligned ROM address
  discovered post-tapeout.
- **64 PMP entries** with 4-byte address-matching support
  ([VeeR EL2 PRM](https://github.com/chipsalliance/Cores-VeeR-EL2),
  `PMP_ENTRIES=64`, `PMP_GRANULARITY=0`). The minimum 4-byte patch
  trap uses the standard PMP `NA4` mode; larger regions, if ever
  needed, would use `NAPOT`. The entry count is far more than any
  realistic patch count; OTP capacity is the actual constraint.

## Design

### Execution Model

Each patch consumes one PMP entry configured as `NA4` (4-byte region),
L=1 (locked, enforced in M-mode), X=0 (no execute). R and W permissions
for the patched 4-byte region are implementation-defined; the entry only
needs to deny instruction fetch. Both the target ROM address and resume
address must be 4-byte aligned.

**RVC alignment constraint.** The minimum PMP region is 4 bytes.
Compressed (RVC) instructions at halfword-aligned addresses cannot be
independently targeted. If the target bug is in an RVC instruction at a
halfword boundary, the patch must target the enclosing 4-byte-aligned
region. The replacement code then covers both the target RVC instruction
and its aligned neighbor. The patch author must account for both
instructions in the replacement.

During boot, after OTP patch verification, MCU ROM:

1. Initializes the trap handler state, including the Trap Control Block
   (TCB) in SRAM and any prologue scratch CSRs.
2. Copies all replacement code into SRAM.
3. Executes `fence.i` so subsequent instruction fetches observe the
   replacement code written to SRAM.
4. Populates the dispatch table (target ROM address → SRAM function
   address + resume offset).
5. Configures PMP entries with L=1, X=0 to mark patched ROM addresses
   as no-execute.

The patch setup code (steps 1–5) is part of the unpatchable core and
must not reside at any patchable ROM address.
No PMP fault can fire before the dispatch infrastructure is ready.
PMP entries are priority ordered, with the lowest-numbered matching
entry determining access. Patch no-execute entries must therefore be
allocated at lower PMP indices than any broader overlapping ROM region,
so the 4-byte `NA4` patch entry wins the permission check.
Locked PMP entries persist until reset. Before mutable MCU firmware
executes, MCI asserts the MCU firmware reset (`BOOT_RST_MCU`), which
resets the MCU core and clears all PMP CSRs. ROM patch PMP entries,
the trap handler state, and the patch SRAM reservation are therefore
live only during the initial ROM boot phase; mutable firmware starts
after reset with a clean PMP configuration.

If multiple non-empty OTP slots target the same ROM address, ROM treats
the highest-numbered slot as authoritative for that address. Only that
slot may populate the dispatch table, and only one PMP entry is
configured for the target address. Earlier slots for the same address
are ignored and cannot become active again, even if the authoritative
slot fails verification or validation.

#### Worked Example

Consider a ROM bug in the PLL divider configuration at address
`0x0000_1040`. The original ROM code writes an incorrect divider value:

```
ROM (original):
  0x1040:  li  a0, 0x3       # wrong divider (bug)
  0x1044:  sw  a0, 0(a1)     # write to PLL register
  0x1048:  nop               # (next instruction)
```

A patch targets address `0x1040` with `resume_offset = 1` (resume at
`0x1040 + 1×4 = 0x1044`), replacing only the incorrect immediate load:

```
Patch replacement (SRAM):
  void patch_pll_fix(trap_frame_t *frame) {
      frame->a0 = 0x5;        // correct divider value
      // mepc already set to 0x1044 by handler (resume_offset=1)
      // the original sw a0, 0(a1) then writes the corrected value
  }
```

At runtime:
1. MCU fetches `0x1040` → PMP fault (entry is locked no-execute).
2. Trap handler saves context, looks up `0x1040` in dispatch table.
3. Handler sets `mepc = 0x1044`, calls `patch_pll_fix(frame)`.
4. Patch modifies `a0` in the saved frame.
5. Handler restores context, `mret` → execution resumes at `0x1044`.

### Trap Sequence

All machine traps enter through a single handler at `mtvec`. The
handler uses a dedicated trap stack in SRAM, separate from the boot
stack. The TCB holds the trap stack bounds, dispatch table base, nesting
depth counter, and any scratch state required by the assembly prologue.

The sequence on each trap:

1. **Prologue and frame allocation.** The assembly prologue switches to
   the dedicated trap stack, allocates an independent trap frame, and
   saves the interrupted GPRs plus `mstatus`, `mepc`, `mcause`, and
   `mtval`. The prologue must support synchronous nested traps without
   consuming or corrupting the interrupted boot stack.

2. **Dispatch.** Call the C trap handler with the frame pointer in `a0`.
   The handler checks `mcause`:
   - Instruction access fault (`mcause = 1`) + `mepc` matches dispatch
     table → **patch fault.** Precompute resume PC as
     `target + resume_offset × 4`,
     write to saved `mepc`, call `void patch_fn(trap_frame_t *frame)`.
   - Instruction access fault + `mepc` not in table → **fatal** (PMP
     misconfiguration or unexpected fetch fault).
   - Other `mcause` → route to non-patch exception path.

3. **Replacement function.** Receives `trap_frame_t *frame` in `a0`.
   May inspect and modify saved GPRs and `mepc` in the frame. Must not
   write CSRs unless explicitly allowed by the patch ABI (see
   [CSR Allowlist](#csr-allowlist)). Returns via `ret` to the trap
   handler (not directly to ROM).

4. **Teardown.** Restore `mepc` and `mstatus` from the possibly
   modified frame, restore the interrupted GPRs, release the trap frame,
   restore the interrupted stack context, and return with `mret`.

### Nesting

The handler supports synchronous nested patch faults: patched code that
calls a ROM function which itself has a patch. MIE stays clear for the
entire trap path — the nesting model is synchronous re-entry, not
interrupt preemption.

The exact prologue/epilogue sequence is implementation-specific, but it
must preserve the following invariant: every trap level allocates an
independent frame on the dedicated trap stack, and returning from an
inner trap restores the outer trap's execution context exactly.

**Nesting depth limit.** The TCB maintains a depth counter incremented
on entry and decremented on exit. If the depth exceeds the configured
maximum (determined by trap stack sizing), the handler treats it as a
fatal error — this indicates a patching cycle or unexpectedly deep call
chain. The maximum nesting depth is set at build time based on:

```
trap_stack_size ≥ (trap_frame_size + max_patch_stack_usage) × max_nesting_depth
```

A practical default is `max_nesting_depth = 4`. Deeper nesting indicates
a design problem in the patches themselves.

### CSR Allowlist

Replacement functions may read CSRs, but must not perform semantic CSR
writes unless the patch ABI explicitly allowlists the target CSR. Patch
ABI version 1 allowlists no CSR writes. This fail-closed policy protects
trap-critical CSRs such as `mscratch`, `mstatus`, `mtvec`, `mepc`,
`mcause`, `mtval`, `mie`, delegation CSRs, and PMP CSRs, and also avoids
implicitly permitting future or implementation-specific CSR side
effects.

**Enforcement.** The patch build tool disassembles the compiled
replacement binary and scans for CSR write instructions. A CSR
instruction is classified as a semantic write using standard RISC-V ISA
rules:

- `csrrw` / `csrrwi`: always writes the CSR (regardless of `rd`).
- `csrrs` / `csrrsi`: writes (sets bits) if `rs1 != x0`. When
  `rs1 = x0`, the instruction is a pure read (`csrr` pseudo).
- `csrrc` / `csrrci`: writes (clears bits) if `rs1 != x0`. When
  `rs1 = x0`, the instruction is a pure read.

The tool rejects the patch if any semantic CSR write is found and the
target CSR is not allowlisted by the patch ABI version. Because RISC-V
CSR instructions encode the CSR number as an immediate field, this
final-binary scan catches standard CSR writes. The tool must scan all
executable sections included in the signed replacement code.

### Patch ABI

Replacement code is a single signed executable blob called from the trap
handler as `void patch_fn(trap_frame_t *frame)`. It executes in the same
M-mode ROM boot context as the code it replaces. Authenticated patches
are trusted as ROM-equivalent code for the duration of MCU ROM boot,
authorized by Ed25519 verification and OTP key provisioning.

Patch ABI requirements:

- Final signed binary is fully linked, position-independent, and
  relocation-free; ROM does not perform dynamic relocation.
- Executable code and read-only constants are allowed. `.data`, `.bss`,
  TLS, heap allocation, constructors, runtime initialization, and
  mutable global state are not allowed.
- GOT/global-pointer based code is allowed only if resolved entirely
  within the blob; otherwise the build tool rejects it.
- Replacement code runs on the dedicated trap stack and must fit within
  `max_patch_stack_usage`.
- Replacement code returns to the trap handler with `ret`; it must not
  execute `mret` or branch directly back to ROM.
- ROM callbacks must go through the exported ROM symbol table and only
  call functions annotated safe for trap-context invocation (no
  trap-critical CSR writes, no normal boot stack assumptions). Patch
  code may load callback entries directly from this fixed ROM table.

### OTP Patch Authentication

Patch blocks reside in `VENDOR_NON_SECRET_PROD_PARTITION`. Each slot is
independently signed and can be burned at different lifecycle stages.
OTP bits transition 0→1 only — a burned block cannot be erased.

MCU ROM reads the Ed25519 public key from a locked OTP fuse, then
processes patch slots in slot order. Before verification, ROM parses
only the minimal fields needed for supersession and failure policy:
header flags, target address, and code size. These fields are not
trusted for applying a patch until the signature verifies. The
pre-verification `code_size` is used only to bound parsing within the
OTP slot and signature payload; ROM must reject any size that exceeds
the slot or patch SRAM region before copying code.

- All-zeros slots → skip (no verification needed).
- Non-empty slots → record the slot as the current authoritative slot
  for its target address, superseding any earlier slot for that same
  address.

After the scan, MCU ROM verifies and validates only the authoritative
slot for each target address. If an authoritative slot fails signature
verification or validation, ROM records the appropriate `PATCH_STATUS`
bit and leaves that target address unpatched. It must not fall back to
an earlier slot for the same address.

Supersession grouping uses the target address parsed from each slot
before signature verification. If a non-empty slot's target address
field is unparseable, it cannot participate in supersession grouping;
earlier slots for any target address remain unaffected. When a newer
slot's target field remains parseable, the no-fallback rule applies.
Security-critical patches should use `CRITICAL=1` so corruption of
newer slot metadata fails closed after the slot header is readable.

Later non-empty blocks targeting the same ROM address supersede earlier
ones by slot order.

**Signature scope.** The Ed25519 signature covers the full patch
payload after the signature field: header word, target address, resume
offset, code size, and replacement instructions. Different products or
ROM versions use different signing keys, preventing a patch built for
one ROM image from being applied to another.

**Why Ed25519 over PQC?** ML-DSA signatures (2420–4627 bytes) do not
fit in OTP. The OTP threat model is physical — reprogramming fuses
requires physical access, which already enables more powerful attacks
than signature forgery.

### Ed25519 Verification Requirements

Patch signatures use pure Ed25519 as specified by RFC 8032; Ed25519ph
and Ed25519ctx are not used. The ROM implementation must:

- Pass RFC 8032 known-answer tests and malformed-signature negative
  tests.
- Use a strict verification implementation that enforces RFC 8032
  encoding requirements and rejects malformed keys and signatures.
- Treat parser errors, unsupported format versions, non-canonical
  encodings, and verification failures as patch validation failures.
- Read the Ed25519 public key from a locked OTP fuse; production devices
  must lock this fuse before patch verification is used as an
  authorization boundary.
- Harden the unpatchable verification path against simple fault
  injection by verifying twice, clearing intermediate results between
  attempts, and requiring both attempts to agree before accepting a
  patch.

### Patch Block Format

Little-endian, naturally aligned:

| Offset | Size | Field |
|--------|------|-------|
| 0x00 | 64 B | Ed25519 signature (over bytes 0x40 – end) |
| 0x40 | 4 B  | Header word: magic/version/flags |
| 0x44 | 4 B  | Target ROM address (absolute, within ROM range) |
| 0x48 | 2 B  | Resume offset (4-byte words from target) |
| 0x4A | 2 B  | Code size (4-byte words, 0–65535) |
| 0x4C | N×4 B | Replacement instructions (RV32IMC, PIC) |

The header word is encoded as:

| Bits | Field |
|------|-------|
| 31:24 | Magic (`0xA5`) |
| 23:16 | Patch format version |
| 15:1 | Reserved, must be zero |
| 0 | `CRITICAL` |

The patch format version covers both the OTP record encoding and the
trap-frame ABI exposed to replacement code. ROM supports only known
versions. Unknown versions, invalid magic values, non-zero reserved
bits, or unsupported flags cause the authoritative slot to fail
validation.

Flags are parsed before signature verification only to choose failure
policy; they never authorize applying code before signature
verification. Flags are also covered by the Ed25519 signature. If the
authoritative slot has `CRITICAL=1`, any failure for that slot,
including signature verification failure, validation failure, copy
failure, or PMP configuration failure, is fatal. Since OTP bits are
one-way 0→1, an already-burned critical patch cannot be downgraded to
optional by fuse corruption. Setting `CRITICAL` on an optional patch can
only make failure more restrictive. This can create a denial-of-service
condition, but only under the physical OTP modification threat model
where denial of service is already possible.

The build tool must reject `resume_offset = 0` (infinite trap loop) and
`code_size = 0` (no replacement code).
RVC instructions are supported within replacement code (the compiler may
pack two 16-bit compressed instructions into a single 4-byte word slot)
but do not affect patch boundary alignment — both the target and resume
addresses must be 4-byte aligned.

### SRAM Memory Map

The patch infrastructure reserves a fixed region at the bottom of the
512 KB MCU SRAM, within the MCI `fw_sram_exec_region_size`. It contains:

- Trap Control Block: trap stack bounds, dispatch table base, nesting
  depth, and prologue scratch state.
- Trap stack.
- Dispatch table: `target_addr`, SRAM function address, and
  `resume_offset`; searched by linear scan.
- Patch code region, sized to OTP capacity.

The TCB and trap stack are live while PMP patch entries are active and
must not be overwritten during ROM boot. They do not impose a permanent
mutable-firmware SRAM reservation because `BOOT_RST_MCU` clears patch
state before mutable firmware starts. The dispatch table and patch code
region must be within the exec region so the MCU can fetch instructions
from SRAM during ROM boot.

### Boot Sequence Integration

Patching occurs during MCU ROM boot, after MCI releases the MCU from
reset and before writing fuses to Caliptra Core or asserting
`CPTRA_BOOT_GO`. SRAM is zeroed by integrator BIST before
`cptra_ss_rst_b` deasserts.

### Error Handling

All patching failures are **non-fatal** by default. ROM continues with
original (unpatched) functions. This preserves device survivability: a
malformed, partially programmed, or corrupted optional patch must not
brick a device that would otherwise boot correctly.

The table below describes the reference non-critical behavior. If the
failing authoritative slot has `CRITICAL=1`, the same failures enter the
fatal boot failure path instead.

A per-slot `CRITICAL` flag can only affect failures after ROM has read
the authoritative slot header. If OTP DAI read fails before slot headers
can be read, ROM cannot determine whether any slot is critical; that
failure remains non-fatal.

| Failure | Non-critical behavior | Status Bit |
|---------|----------|------------|
| OTP DAI read fails | Skip patching | `PATCH_STATUS.OTP_READ_FAIL` |
| Ed25519 signature invalid | Skip block | `PATCH_STATUS.OTP_SIG_FAIL` |
| Target outside ROM range | Skip entry | `PATCH_STATUS.INVALID_ADDR` |
| Code exceeds patch region | Reject patch | `PATCH_STATUS.SIZE_EXCEEDED` |
| Code size is 0 | Skip entry | `PATCH_STATUS.EMPTY_ENTRY` |
| Overlapping PMP regions | Skip entry | `PATCH_STATUS.OVERLAP` |

`PATCH_STATUS` is a 32-bit word written to the MCI trace buffer at a
fixed offset. The status word itself is informational and does not
trigger MCI error aggregation or fatal/non-fatal interrupt outputs; fatal
behavior is controlled by `CRITICAL`.
CRM or debug tooling can read it post-boot to determine whether patching
succeeded.

`PATCH_STATUS` bits are sticky aggregate indicators across all processed
patch slots; they report that at least one slot encountered the
condition, not which slot encountered it. Per-authoritative-slot
validation results are reported through the supplemental DPE measurement
when patching is enabled.

## Unpatchable Core

The following ROM code executes before the patching infrastructure is
ready and **cannot be patched**:

- Reset vector and initial stack setup
- PMP trap handler (prologue + epilogue + dispatch)
- OTP DAI read sequence for patch and key fuses
- Ed25519 signature verification (~10–12 KB)
- PMP configuration and dispatch table population

This code must be correct at tapeout. It should be minimized and
reviewed with the same rigor as RTL. Any bug here requires a metal
respin or a silicon workaround at the SoC level. As a countermeasure
against fault injection on signature verification, the implementation
should perform double verification (verify, clear result, verify again,
compare) within this critical path.

## DICE Impact

MCU ROM is **not** part of the DICE measurement chain. DICE measures
Caliptra Core code (ROM, FMC, Runtime). MCU ROM patches do not
participate in CDI derivation or key generation.

When MCU ROM patching is enabled, MCU ROM records a supplemental
measurement into Caliptra's DPE context via the `STASH_MEASUREMENT`
mailbox command. The measurement represents effective MCU ROM patch
state: MCU mask ROM identity or digest, patch format version,
`PATCH_STATUS`, authoritative slot index and target address per target,
validation result, and the signed-payload hash for each readable
authoritative slot. If a candidate or authoritative slot cannot be read,
the measurement records slot index, target address if available, and
read-failure status, but no payload hash.

Non-authoritative slots are excluded because they cannot affect
execution. Implementations may add a separate audit measurement covering
all raw OTP patch slot contents if manufacturing or debug tooling needs
full fuse provenance.

## Threat Model

### Attacker Model

The primary threat is a post-silicon ROM bug that needs a field fix. The
patching mechanism itself introduces a secondary attack surface. We
consider two attacker classes:

- **Software-only attacker** (remote or local unprivileged). Cannot
  influence ROM patching. Patches are burned in OTP and verified before
  the MCU runs any mutable code. The attacker has no write access to
  SRAM during the patch setup window (MCU ROM boot before
  `CPTRA_BOOT_GO`).

- **Physical attacker** (fault injection, probing, FIB). Can
  potentially glitch the Ed25519 verification, modify SRAM contents
  via voltage glitching, or probe OTP fuse values. This class is
  bounded by the Caliptra SS physical attack mitigations (lifecycle
  gating, debug lock, anti-tamper) which are outside the scope of this
  RFC.

### Specific Threats

| Threat | Mitigation |
|--------|------------|
| **Unauthorized patch injection** | Ed25519 signature verification using a locked OTP public key. |
| **Cross-product patch replay** | Per-product / per-ROM-version signing keys. |
| **SRAM tampering after verification** | MCU-only early boot window plus MCI AXI USER filtering. |
| **Fault injection on Ed25519 verify** | Double verification with cleared intermediate state. |
| **Dispatch table corruption** | Same early-boot SRAM integrity assumptions as patch code. |
| **Rollback / supersession** | Highest-numbered same-target slot wins when the target field remains parseable; security patches use `CRITICAL=1` to fail closed. |

### Lifecycle Interaction

- **Manufacturing / Debug lifecycle:** Debug interfaces may be open.
  Patches can be provisioned but their security depends on physical
  access controls in the manufacturing environment.
- **Production lifecycle:** Debug interfaces are gated. PMP entries
  with L=1 cannot be reconfigured. The VeeR EL2 debug mode can
  override PMP in debug lifecycle states, but not in production.
- **Patch provisioning** uses the Caliptra key provisioning
  infrastructure. Only entities with access to the Ed25519 private key
  can produce valid patches. Key management is outside the scope of
  this RFC.

## Implementation Tradeoffs

| Aspect | Cost |
|--------|------|
| ROM size | +10–12 KB (Ed25519 implementation) |
| Trap overhead | Register save/restore + dispatch per patched call site (negligible for boot code that executes once) |
| OTP consumption | 64 B signature + 12 B header + replacement code per patch block |
| SRAM reservation | TCB + trap stack + dispatch table + patch code region |
| Patch ABI | Replacement code runs as trap callback, not direct function replacement |
| Unpatchable core | ~12–15 KB of ROM code must be correct at tapeout |

## Patch Toolchain

1. **Identify target.** From ROM ELF/map, determine the ROM address and
   resume address.
2. **Write replacement.** C or assembly, built as position-independent
   and relocation-free code, using the ROM symbol table for callbacks.
3. **Build and sign.** Tool packs target address, resume offset, code
   into the patch block format, runs the CSR allowlist check, and signs
   with the Ed25519 private key.
4. **Produce fuse image.** Convert signed block to OTP programming
   image.

Steps 3–4 should be a single automated tool that takes a patch
description (target address, resume address, replacement source file)
and produces a signed fuse image.

## OTP Partition Requirements

Fuses in `VENDOR_NON_SECRET_PROD_PARTITION` via
`gen_fuse_ctrl_partitions.yml`:

| Slot | Size | Purpose |
|------|------|---------|
| 0 | 32 B | Ed25519 public key |
| 1–N | Configurable | Patch block slots (independently signed) |

**Reference configuration:** 8 slots × 256 bytes each = 2 KB total OTP.
Each slot supports up to 45 words (180 bytes) of replacement code after
the 64-byte signature and 12-byte header. This is sufficient for common
small ROM fixes such as changing a register value, replacing an MMIO
write sequence, or branching through a ROM helper. The number of slots
and their sizes are set by the integrator via
`gen_fuse_ctrl_partitions.yml` based on OTP budget and expected patch
complexity; products that expect larger C replacements can allocate
larger patch slots. If no patches are needed at tapeout, the region can
be left unburned (all-zeros); MCU ROM detects and skips empty slots.
