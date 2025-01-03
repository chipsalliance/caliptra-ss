<!--
DO NOT EDIT THIS FILE DIRECTLY.
It has been generated with ./util/design/gen-otp-mmap.py
-->

|    Partition     |  Secret  |  Buffered  |  Integrity  |  WR Lockable  |  RD Lockable  | Description                                                         |
|:----------------:|:--------:|:----------:|:-----------:|:-------------:|:-------------:|:--------------------------------------------------------------------|
|   VENDOR_TEST    |    no    |     no     |     no      | yes (Digest)  |   yes (CSR)   | Vendor test partition.                                              |
|                  |          |            |             |               |               | This is reserved for manufacturing smoke checks. The OTP wrapper    |
|                  |          |            |             |               |               | control logic inside prim_otp is allowed to read/write to this      |
|                  |          |            |             |               |               | region. ECC uncorrectable errors seen on the functional prim_otp    |
|                  |          |            |             |               |               | interface will not lead to an alert for this partition.             |
|                  |          |            |             |               |               | Instead, such errors will be reported as correctable ECC errors.    |
| NON_SECRET_FUSES |    no    |     no     |     yes     | yes (Digest)  |   yes (CSR)   | Non Secret Fuses partition.                                         |
|                  |          |            |             |               |               | This contains data such IDEVID, public key hash mask, owner         |
|                  |          |            |             |               |               | key hash, SoC Stepping ID etc.                                      |
|     SECRET0      |   yes    |    yes     |     yes     | yes (Digest)  | yes (Digest)  | Secret partition 0.                                                 |
|                  |          |            |             |               |               | This contains Obfuscated UDS seed.                                  |
|     SECRET1      |   yes    |    yes     |     yes     | yes (Digest)  | yes (Digest)  | Secret partition 1.                                                 |
|                  |          |            |             |               |               | This contains obfuscated field entropy.                             |
|     SECRET2      |   yes    |    yes     |     yes     | yes (Digest)  | yes (Digest)  | Secret partition 2.                                                 |
|                  |          |            |             |               |               | This contains public key hash.                                      |
|    LIFE_CYCLE    |    no    |    yes     |     yes     |      no       |      no       | Lifecycle partition.                                                |
|                  |          |            |             |               |               | This contains lifecycle transition count and state. This partition  |
|                  |          |            |             |               |               | cannot be locked since the life cycle state needs to advance to RMA |
|                  |          |            |             |               |               | in-field. Note that while this partition is not marked secret, it   |
|                  |          |            |             |               |               | is not readable nor writeable via the DAI. Only the LC controller   |
|                  |          |            |             |               |               | can access this partition, and even via the LC controller it is not |
|                  |          |            |             |               |               | possible to read the raw manufacturing life cycle state in encoded  |
|                  |          |            |             |               |               | form, since that encoding is considered a netlist secret. The LC    |
|                  |          |            |             |               |               | controller only exposes a decoded version of this state.            |
