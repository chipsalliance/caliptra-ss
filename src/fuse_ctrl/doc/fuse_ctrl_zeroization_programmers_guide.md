# Zeroization Programmer's Guide

As of version 2.1, the Caliptra subsystem complies with the [OCP L.O.C.K.](https://github.com/chipsalliance/Caliptra/blob/main/doc/ocp_lock/lock_spec.ocp) specification for secure cryptographic key management.
Zeroization of sensitive keys is a core component of the protocol, which for the `fuse_ctrl` means that it needs to support overwriting already programmed and locked partitions.
This document describes how provisioners can interact with the direct-access interface (DAI) to achieve the zeroization of a partition.

## Enabling Zeroization

Zeroization is a build-time parameter that governs for each partition whether it can be zeroized during its life cycle.
It can be found in the [MMAP](../data/otp_ctrl_mmap.hjson) alongside the other conventional parameters that instrument a partition.
Every partition type except `LIFE_CYCLE` can be zeroizable regardless of whether it is a hardware or software partition.
When a partition is marked as zeroizable, the partition generation [script](../../../tools/scripts/fuse_ctrl_script/gen_fuse_ctrl_partitions.py) inserts a 64-bit fuse at the end of the partition that serves as an indicator for the `fuse_ctrl` to detect when a partition is zeroized or in the process of being zeroized.
The detection criteria is explained later in the document.

## Zeroization Flow

Zeroizing a partition is completely handled by firmware and resembles an ordinary in-field provisioning flow.

1. The DAI has a dedicated `ZEROIZE` command through which a word (either 32-bit for software fuses or 64-bit for hardware fuses including the digest and zeroization fields) in a partition can be zeroized.
The entire address space of a partition is zeroizable which contrasts with the other DAI commands.
For example, the digest field is never writable through the `WRITE` command in a hardware partition.

    > Side effect: The `fuse_ctrl` detects the first _successful_ word zeroization and disables periodic consistency checks for the corresponding partition as these can potentially fail when interrupting an ongoing zeroization procedure.
    Integrity checks for hardware partitions can proceed normally until the next reset as they only act on buffered data.
    
   Although the fuses of a partition can be zeroized in any order, it is recommended to first zeroize the zeroization field at the end of a partition to mark it as zeroized or being zeroized in the case the flow is interrupted and needs to be resumed at a later point.

    > Side effect: A fuse macro usually signals an error if a write attempts to clear an already set data or ECC bit.
    > Such an unintended bit flip can occur in the ECC part of a word during a zeroization (when only the data part is zeroized), hence the `ZEROIZE` command disables ECC when zeroizing a word, setting all bits in both the data and ECC part of a fuse word.

  2. A successful zeroization of a fuse word results in the zeroized word being returned to software in the `DIRECT_ACCESS_RDATA` registers for inspection bypassing the
  descrambling mechanism if the word belongs to a secret partition.
  This is the only way firmware can confirm, in the absence of a malicious tampering attempt, whether a fuse has been cleared.
  The `ZEROIZE` command is idempotent, i.e., it can be retried multiple times such that a zeroization of an already zeroized word has no effect.

  3. When firmware determines that a partition has been sufficiently zeroized, it should reset the `fuse_ctrl` such that the zeroized data is also reflected in the buffer registers.

     > Side effect: Upon initialization, the `fuse_ctrl` will first read the zeroization field of a partition to determine whether it is in a zeroized state.
    If so, no periodic consistency and integrity checks will be executed for the partition.

## Zeroization Detection

There are two distinct cases when the `fuse_ctrl` performs a zeroization detection by counting the number of set bits in a word and comparing the resulting value against predefined thresholds that account for potentially stuck-at-0 bits.

  1. _Initialization_: As mentioned above, the periodic consistency and integrity checks need to be disabled for a zeroized partition, furthermore when reading out the content of buffered partitions, the ECC checks need to be disabled.
  This means that the zeroization indicator field has to be checked first before performing the remaining initialization steps.
  A partition is said to be in a zeroized state if and only if the number of set bits in the indicator field is greater or equal the macro-specific value `ZeroizationValidBound`.
  This bound should include a margin that accounts for defects where certain fuse bits are perpetually stuck at 0.
  2. _Scrambled Zeroization_: As the zeroization flow requires that zeroized words are returned back to firmware for inspection, there is a possibility that scrambled data is released unintentionally either through an error case or a malicious fault attack.
  The `fuse_ctrl` guards against this case with by screening each zeroized word.
  First, whenever the OTP macro signals an error in response to a zeroization request, no data is released.
  Second, for scrambled partitions, the zeroized fuse is only returned if and only if the number of set bits in the 64-bit word is greater or equal `ZeroizationValidBound`.
  If a zeroized word does not meet this criterion, then firmware should continue erasing the remaining parts of a partition and retry the faulty erasure at a later point.
  An escalation should be triggered, if repeated zeroizations fall below `ZeroizationValidBound`.
  The `ZeroizationValidBound` should be chosen such that the probability that a scrambled word is accidentally recognized as zeroized is as small as possible while still accounting for potentially stuck-at-0 bits.
  The problem of returning a zeroized word makes it impossible to have a mechanism that has a 0% probability of ever releasing a scrambled word to firmware, however even if this low-probability case occurs, the scrambling key remains secret making it unlikely that the word can be descrambled.
  Assuming that most bits are set after a zeroization, even if the scrambling key became compromised, it would be impossible to retrieve individual bits of a zeroized word.
  Note that is is impossible that the `fuse_ctrl` ever releases a descrambled word in any scenario.