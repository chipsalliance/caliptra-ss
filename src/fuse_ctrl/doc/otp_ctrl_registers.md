## Summary of the **`core`** interface's registers

| Name                                                                                                   | Offset   |   Length | Description                                                                                         |
|:-------------------------------------------------------------------------------------------------------|:---------|---------:|:----------------------------------------------------------------------------------------------------|
| otp_ctrl.[`INTR_STATE`](#intr_state)                                                                   | 0x0      |        4 | Interrupt State Register                                                                            |
| otp_ctrl.[`INTR_ENABLE`](#intr_enable)                                                                 | 0x4      |        4 | Interrupt Enable Register                                                                           |
| otp_ctrl.[`INTR_TEST`](#intr_test)                                                                     | 0x8      |        4 | Interrupt Test Register                                                                             |
| otp_ctrl.[`ALERT_TEST`](#alert_test)                                                                   | 0xc      |        4 | Alert Test Register                                                                                 |
| otp_ctrl.[`STATUS`](#status)                                                                           | 0x10     |        4 | OTP status register.                                                                                |
| otp_ctrl.[`ERR_CODE_0`](#err_code)                                                                     | 0x14     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_1`](#err_code)                                                                     | 0x18     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_2`](#err_code)                                                                     | 0x1c     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_3`](#err_code)                                                                     | 0x20     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_4`](#err_code)                                                                     | 0x24     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_5`](#err_code)                                                                     | 0x28     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_6`](#err_code)                                                                     | 0x2c     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_7`](#err_code)                                                                     | 0x30     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_8`](#err_code)                                                                     | 0x34     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_9`](#err_code)                                                                     | 0x38     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_10`](#err_code)                                                                    | 0x3c     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_11`](#err_code)                                                                    | 0x40     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_12`](#err_code)                                                                    | 0x44     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_13`](#err_code)                                                                    | 0x48     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_14`](#err_code)                                                                    | 0x4c     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_15`](#err_code)                                                                    | 0x50     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_16`](#err_code)                                                                    | 0x54     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_17`](#err_code)                                                                    | 0x58     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)                                               | 0x5c     |        4 | Register write enable for all direct access interface registers.                                    |
| otp_ctrl.[`DIRECT_ACCESS_CMD`](#direct_access_cmd)                                                     | 0x60     |        4 | Command register for direct accesses.                                                               |
| otp_ctrl.[`DIRECT_ACCESS_ADDRESS`](#direct_access_address)                                             | 0x64     |        4 | Address register for direct accesses.                                                               |
| otp_ctrl.[`DIRECT_ACCESS_WDATA_0`](#direct_access_wdata)                                               | 0x68     |        4 | Write data for direct accesses.                                                                     |
| otp_ctrl.[`DIRECT_ACCESS_WDATA_1`](#direct_access_wdata)                                               | 0x6c     |        4 | Write data for direct accesses.                                                                     |
| otp_ctrl.[`DIRECT_ACCESS_RDATA_0`](#direct_access_rdata)                                               | 0x70     |        4 | Read data for direct accesses.                                                                      |
| otp_ctrl.[`DIRECT_ACCESS_RDATA_1`](#direct_access_rdata)                                               | 0x74     |        4 | Read data for direct accesses.                                                                      |
| otp_ctrl.[`CHECK_TRIGGER_REGWEN`](#check_trigger_regwen)                                               | 0x78     |        4 | Register write enable for !!CHECK_TRIGGER.                                                          |
| otp_ctrl.[`CHECK_TRIGGER`](#check_trigger)                                                             | 0x7c     |        4 | Command register for direct accesses.                                                               |
| otp_ctrl.[`CHECK_REGWEN`](#check_regwen)                                                               | 0x80     |        4 | Register write enable for !!INTEGRITY_CHECK_PERIOD and !!CONSISTENCY_CHECK_PERIOD.                  |
| otp_ctrl.[`CHECK_TIMEOUT`](#check_timeout)                                                             | 0x84     |        4 | Timeout value for the integrity and consistency checks.                                             |
| otp_ctrl.[`INTEGRITY_CHECK_PERIOD`](#integrity_check_period)                                           | 0x88     |        4 | This value specifies the maximum period that can be generated pseudo-randomly.                      |
| otp_ctrl.[`CONSISTENCY_CHECK_PERIOD`](#consistency_check_period)                                       | 0x8c     |        4 | This value specifies the maximum period that can be generated pseudo-randomly.                      |
| otp_ctrl.[`SW_MANUF_PARTITION_READ_LOCK`](#sw_manuf_partition_read_lock)                               | 0x90     |        4 | Runtime read lock for the SW_MANUF_PARTITION partition.                                             |
| otp_ctrl.[`SVN_PARTITION_READ_LOCK`](#svn_partition_read_lock)                                         | 0x94     |        4 | Runtime read lock for the SVN_PARTITION partition.                                                  |
| otp_ctrl.[`VENDOR_TEST_PARTITION_READ_LOCK`](#vendor_test_partition_read_lock)                         | 0x98     |        4 | Runtime read lock for the VENDOR_TEST_PARTITION partition.                                          |
| otp_ctrl.[`VENDOR_HASHES_MANUF_PARTITION_READ_LOCK`](#vendor_hashes_manuf_partition_read_lock)         | 0x9c     |        4 | Runtime read lock for the VENDOR_HASHES_MANUF_PARTITION partition.                                  |
| otp_ctrl.[`VENDOR_HASHES_PROD_PARTITION_READ_LOCK`](#vendor_hashes_prod_partition_read_lock)           | 0xa0     |        4 | Runtime read lock for the VENDOR_HASHES_PROD_PARTITION partition.                                   |
| otp_ctrl.[`VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK`](#vendor_revocations_prod_partition_read_lock) | 0xa4     |        4 | Runtime read lock for the VENDOR_REVOCATIONS_PROD_PARTITION partition.                              |
| otp_ctrl.[`VENDOR_NON_SECRET_PROD_PARTITION_READ_LOCK`](#vendor_non_secret_prod_partition_read_lock)   | 0xa8     |        4 | Runtime read lock for the VENDOR_NON_SECRET_PROD_PARTITION partition.                               |
| otp_ctrl.[`VENDOR_PK_HASH_VOLATILE_LOCK`](#vendor_pk_hash_volatile_lock)                               | 0xac     |        4 | Address register for direct accesses.                                                               |
| otp_ctrl.[`SW_TEST_UNLOCK_PARTITION_DIGEST_0`](#sw_test_unlock_partition_digest)                       | 0xb0     |        4 | Integrity digest for the SW_TEST_UNLOCK_PARTITION partition.                                        |
| otp_ctrl.[`SW_TEST_UNLOCK_PARTITION_DIGEST_1`](#sw_test_unlock_partition_digest)                       | 0xb4     |        4 | Integrity digest for the SW_TEST_UNLOCK_PARTITION partition.                                        |
| otp_ctrl.[`SECRET_MANUF_PARTITION_DIGEST_0`](#secret_manuf_partition_digest)                           | 0xb8     |        4 | Integrity digest for the SECRET_MANUF_PARTITION partition.                                          |
| otp_ctrl.[`SECRET_MANUF_PARTITION_DIGEST_1`](#secret_manuf_partition_digest)                           | 0xbc     |        4 | Integrity digest for the SECRET_MANUF_PARTITION partition.                                          |
| otp_ctrl.[`SECRET_PROD_PARTITION_0_DIGEST_0`](#secret_prod_partition_0_digest)                         | 0xc0     |        4 | Integrity digest for the SECRET_PROD_PARTITION_0 partition.                                         |
| otp_ctrl.[`SECRET_PROD_PARTITION_0_DIGEST_1`](#secret_prod_partition_0_digest)                         | 0xc4     |        4 | Integrity digest for the SECRET_PROD_PARTITION_0 partition.                                         |
| otp_ctrl.[`SECRET_PROD_PARTITION_1_DIGEST_0`](#secret_prod_partition_1_digest)                         | 0xc8     |        4 | Integrity digest for the SECRET_PROD_PARTITION_1 partition.                                         |
| otp_ctrl.[`SECRET_PROD_PARTITION_1_DIGEST_1`](#secret_prod_partition_1_digest)                         | 0xcc     |        4 | Integrity digest for the SECRET_PROD_PARTITION_1 partition.                                         |
| otp_ctrl.[`SECRET_PROD_PARTITION_2_DIGEST_0`](#secret_prod_partition_2_digest)                         | 0xd0     |        4 | Integrity digest for the SECRET_PROD_PARTITION_2 partition.                                         |
| otp_ctrl.[`SECRET_PROD_PARTITION_2_DIGEST_1`](#secret_prod_partition_2_digest)                         | 0xd4     |        4 | Integrity digest for the SECRET_PROD_PARTITION_2 partition.                                         |
| otp_ctrl.[`SECRET_PROD_PARTITION_3_DIGEST_0`](#secret_prod_partition_3_digest)                         | 0xd8     |        4 | Integrity digest for the SECRET_PROD_PARTITION_3 partition.                                         |
| otp_ctrl.[`SECRET_PROD_PARTITION_3_DIGEST_1`](#secret_prod_partition_3_digest)                         | 0xdc     |        4 | Integrity digest for the SECRET_PROD_PARTITION_3 partition.                                         |
| otp_ctrl.[`SW_MANUF_PARTITION_DIGEST_0`](#sw_manuf_partition_digest)                                   | 0xe0     |        4 | Integrity digest for the SW_MANUF_PARTITION partition.                                              |
| otp_ctrl.[`SW_MANUF_PARTITION_DIGEST_1`](#sw_manuf_partition_digest)                                   | 0xe4     |        4 | Integrity digest for the SW_MANUF_PARTITION partition.                                              |
| otp_ctrl.[`SECRET_LC_TRANSITION_PARTITION_DIGEST_0`](#secret_lc_transition_partition_digest)           | 0xe8     |        4 | Integrity digest for the SECRET_LC_TRANSITION_PARTITION partition.                                  |
| otp_ctrl.[`SECRET_LC_TRANSITION_PARTITION_DIGEST_1`](#secret_lc_transition_partition_digest)           | 0xec     |        4 | Integrity digest for the SECRET_LC_TRANSITION_PARTITION partition.                                  |
| otp_ctrl.[`VENDOR_TEST_PARTITION_DIGEST_0`](#vendor_test_partition_digest)                             | 0xf0     |        4 | Integrity digest for the VENDOR_TEST_PARTITION partition.                                           |
| otp_ctrl.[`VENDOR_TEST_PARTITION_DIGEST_1`](#vendor_test_partition_digest)                             | 0xf4     |        4 | Integrity digest for the VENDOR_TEST_PARTITION partition.                                           |
| otp_ctrl.[`VENDOR_HASHES_MANUF_PARTITION_DIGEST_0`](#vendor_hashes_manuf_partition_digest)             | 0xf8     |        4 | Integrity digest for the VENDOR_HASHES_MANUF_PARTITION partition.                                   |
| otp_ctrl.[`VENDOR_HASHES_MANUF_PARTITION_DIGEST_1`](#vendor_hashes_manuf_partition_digest)             | 0xfc     |        4 | Integrity digest for the VENDOR_HASHES_MANUF_PARTITION partition.                                   |
| otp_ctrl.[`VENDOR_HASHES_PROD_PARTITION_DIGEST_0`](#vendor_hashes_prod_partition_digest)               | 0x100    |        4 | Integrity digest for the VENDOR_HASHES_PROD_PARTITION partition.                                    |
| otp_ctrl.[`VENDOR_HASHES_PROD_PARTITION_DIGEST_1`](#vendor_hashes_prod_partition_digest)               | 0x104    |        4 | Integrity digest for the VENDOR_HASHES_PROD_PARTITION partition.                                    |
| otp_ctrl.[`VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_0`](#vendor_revocations_prod_partition_digest)     | 0x108    |        4 | Integrity digest for the VENDOR_REVOCATIONS_PROD_PARTITION partition.                               |
| otp_ctrl.[`VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_1`](#vendor_revocations_prod_partition_digest)     | 0x10c    |        4 | Integrity digest for the VENDOR_REVOCATIONS_PROD_PARTITION partition.                               |
| otp_ctrl.[`VENDOR_SECRET_PROD_PARTITION_DIGEST_0`](#vendor_secret_prod_partition_digest)               | 0x110    |        4 | Integrity digest for the VENDOR_SECRET_PROD_PARTITION partition.                                    |
| otp_ctrl.[`VENDOR_SECRET_PROD_PARTITION_DIGEST_1`](#vendor_secret_prod_partition_digest)               | 0x114    |        4 | Integrity digest for the VENDOR_SECRET_PROD_PARTITION partition.                                    |
| otp_ctrl.[`VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_0`](#vendor_non_secret_prod_partition_digest)       | 0x118    |        4 | Integrity digest for the VENDOR_NON_SECRET_PROD_PARTITION partition.                                |
| otp_ctrl.[`VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_1`](#vendor_non_secret_prod_partition_digest)       | 0x11c    |        4 | Integrity digest for the VENDOR_NON_SECRET_PROD_PARTITION partition.                                |
| otp_ctrl.[`SW_CFG_WINDOW`](#sw_cfg_window)                                                             | 0x1000   |     4096 | Any read to this window directly maps to the corresponding offset in the creator and owner software |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "otp_operation_done", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "otp_error", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                                                                      |
|:------:|:------:|:-------:|:-------------------|:-----------------------------------------------------------------------------------------------------------------|
|  31:2  |        |         |                    | Reserved                                                                                                         |
|   1    |  rw1c  |   0x0   | otp_error          | An error has occurred in the OTP controller. Check the [`ERR_CODE`](#err_code) register to get more information. |
|   0    |  rw1c  |   0x0   | otp_operation_done | A direct access command or digest calculation operation has completed.                                           |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "otp_operation_done", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "otp_error", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                                  |
|:------:|:------:|:-------:|:-------------------|:-----------------------------------------------------------------------------|
|  31:2  |        |         |                    | Reserved                                                                     |
|   1    |   rw   |   0x0   | otp_error          | Enable interrupt when [`INTR_STATE.otp_error`](#intr_state) is set.          |
|   0    |   rw   |   0x0   | otp_operation_done | Enable interrupt when [`INTR_STATE.otp_operation_done`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "otp_operation_done", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "otp_error", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                           |
|:------:|:------:|:-------:|:-------------------|:----------------------------------------------------------------------|
|  31:2  |        |         |                    | Reserved                                                              |
|   1    |   wo   |   0x0   | otp_error          | Write 1 to force [`INTR_STATE.otp_error`](#intr_state) to 1.          |
|   0    |   wo   |   0x0   | otp_operation_done | Write 1 to force [`INTR_STATE.otp_operation_done`](#intr_state) to 1. |

## ALERT_TEST
Alert Test Register
- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "fatal_macro_error", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_check_error", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_bus_integ_error", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_prim_otp_alert", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "recov_prim_otp_alert", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                      |
|:------:|:------:|:-------:|:----------------------|:-------------------------------------------------|
|  31:5  |        |         |                       | Reserved                                         |
|   4    |   wo   |   0x0   | recov_prim_otp_alert  | Write 1 to trigger one alert event of this kind. |
|   3    |   wo   |   0x0   | fatal_prim_otp_alert  | Write 1 to trigger one alert event of this kind. |
|   2    |   wo   |   0x0   | fatal_bus_integ_error | Write 1 to trigger one alert event of this kind. |
|   1    |   wo   |   0x0   | fatal_check_error     | Write 1 to trigger one alert event of this kind. |
|   0    |   wo   |   0x0   | fatal_macro_error     | Write 1 to trigger one alert event of this kind. |

## STATUS
OTP status register.
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0xffffff`

### Fields

```wavejson
{"reg": [{"name": "SW_TEST_UNLOCK_PARTITION_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SECRET_MANUF_PARTITION_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SECRET_PROD_PARTITION_0_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SECRET_PROD_PARTITION_1_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SECRET_PROD_PARTITION_2_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SECRET_PROD_PARTITION_3_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SW_MANUF_PARTITION_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SECRET_LC_TRANSITION_PARTITION_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SVN_PARTITION_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VENDOR_TEST_PARTITION_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VENDOR_HASHES_MANUF_PARTITION_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VENDOR_HASHES_PROD_PARTITION_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VENDOR_REVOCATIONS_PROD_PARTITION_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VENDOR_SECRET_PROD_PARTITION_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VENDOR_NON_SECRET_PROD_PARTITION_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "LIFE_CYCLE_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "DAI_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "LCI_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TIMEOUT_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "LFSR_FSM_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SCRAMBLING_FSM_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "BUS_INTEG_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "DAI_IDLE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CHECK_PENDING", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 410}}
```

|  Bits  |  Type  |  Reset  | Name                                    | Description                                                                                                                                           |
|:------:|:------:|:-------:|:----------------------------------------|:------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:24  |        |         |                                         | Reserved                                                                                                                                              |
|   23   |   ro   |   0x0   | CHECK_PENDING                           | Set to 1 if an integrity or consistency check triggered by the LFSR timer or via [`CHECK_TRIGGER`](#check_trigger) is pending.                        |
|   22   |   ro   |   0x0   | DAI_IDLE                                | Set to 1 if the DAI is idle and ready to accept commands.                                                                                             |
|   21   |   ro   |   0x0   | BUS_INTEG_ERROR                         | This bit is set to 1 if a fatal bus integrity fault is detected. This error triggers a fatal_bus_integ_error alert.                                   |
|   20   |   ro   |   0x0   | SCRAMBLING_FSM_ERROR                    | Set to 1 if the scrambling datapath FSM has reached an invalid state. This raises an fatal_check_error alert and is an unrecoverable error condition. |
|   19   |   ro   |   0x0   | LFSR_FSM_ERROR                          | Set to 1 if the LFSR timer FSM has reached an invalid state. This raises an fatal_check_error alert and is an unrecoverable error condition.          |
|   18   |   ro   |   0x0   | TIMEOUT_ERROR                           | Set to 1 if an integrity or consistency check times out. This raises an fatal_check_error alert and is an unrecoverable error condition.              |
|   17   |   ro   |   0x0   | LCI_ERROR                               | Set to 1 if an error occurred in the LCI. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.               |
|   16   |   ro   |   0x0   | DAI_ERROR                               | Set to 1 if an error occurred in the DAI. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.               |
|   15   |   ro   |   0x0   | LIFE_CYCLE_ERROR                        | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   14   |   ro   |   0x0   | VENDOR_NON_SECRET_PROD_PARTITION_ERROR  | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   13   |   ro   |   0x0   | VENDOR_SECRET_PROD_PARTITION_ERROR      | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   12   |   ro   |   0x0   | VENDOR_REVOCATIONS_PROD_PARTITION_ERROR | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   11   |   ro   |   0x0   | VENDOR_HASHES_PROD_PARTITION_ERROR      | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   10   |   ro   |   0x0   | VENDOR_HASHES_MANUF_PARTITION_ERROR     | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   9    |   ro   |   0x0   | VENDOR_TEST_PARTITION_ERROR             | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   8    |   ro   |   0x0   | SVN_PARTITION_ERROR                     | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   7    |   ro   |   0x0   | SECRET_LC_TRANSITION_PARTITION_ERROR    | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   6    |   ro   |   0x0   | SW_MANUF_PARTITION_ERROR                | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   5    |   ro   |   0x0   | SECRET_PROD_PARTITION_3_ERROR           | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   4    |   ro   |   0x0   | SECRET_PROD_PARTITION_2_ERROR           | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   3    |   ro   |   0x0   | SECRET_PROD_PARTITION_1_ERROR           | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   2    |   ro   |   0x0   | SECRET_PROD_PARTITION_0_ERROR           | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   1    |   ro   |   0x0   | SECRET_MANUF_PARTITION_ERROR            | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   0    |   ro   |   0x0   | SW_TEST_UNLOCK_PARTITION_ERROR          | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |

## ERR_CODE
This register holds information about error conditions that occurred in the agents
interacting with the OTP macro via the internal bus. The error codes should be checked
if the partitions, DAI or LCI flag an error in the [`STATUS`](#status) register, or when an
[`INTR_STATE.otp_error`](#intr_state) has been triggered. Note that all errors trigger an otp_error
interrupt, and in addition some errors may trigger either an fatal_macro_error or an
fatal_check_error alert.
- Reset default: `0x0`
- Reset mask: `0x7`

### Instances

| Name        | Offset   |
|:------------|:---------|
| ERR_CODE_0  | 0x14     |
| ERR_CODE_1  | 0x18     |
| ERR_CODE_2  | 0x1c     |
| ERR_CODE_3  | 0x20     |
| ERR_CODE_4  | 0x24     |
| ERR_CODE_5  | 0x28     |
| ERR_CODE_6  | 0x2c     |
| ERR_CODE_7  | 0x30     |
| ERR_CODE_8  | 0x34     |
| ERR_CODE_9  | 0x38     |
| ERR_CODE_10 | 0x3c     |
| ERR_CODE_11 | 0x40     |
| ERR_CODE_12 | 0x44     |
| ERR_CODE_13 | 0x48     |
| ERR_CODE_14 | 0x4c     |
| ERR_CODE_15 | 0x50     |
| ERR_CODE_16 | 0x54     |
| ERR_CODE_17 | 0x58     |


### Fields

```wavejson
{"reg": [{"name": "ERR_CODE", "bits": 3, "attr": ["ro"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name                            |
|:------:|:------:|:-------:|:--------------------------------|
|  31:3  |        |         | Reserved                        |
|  2:0   |   ro   |   0x0   | [ERR_CODE](#err_code--err_code) |

### ERR_CODE . ERR_CODE

| Value   | Name                    | Description                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |
|:--------|:------------------------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x0     | NO_ERROR                | No error condition has occurred.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| 0x1     | MACRO_ERROR             | Returned if the OTP macro command was invalid or did not complete successfully due to a macro malfunction. This error should never occur during normal operation and is not recoverable. This error triggers an fatal_macro_error alert.                                                                                                                                                                                                                                                                                                                                                                             |
| 0x2     | MACRO_ECC_CORR_ERROR    | A correctable ECC error has occured during an OTP read operation. The corresponding controller automatically recovers from this error when issuing a new command.                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| 0x3     | MACRO_ECC_UNCORR_ERROR  | An uncorrectable ECC error has occurred during an OTP read operation. This error should never occur during normal operation and is not recoverable. If this error is present this may be a sign that the device is malfunctioning. This error triggers an fatal_macro_error alert.                                                                                                                                                                                                                                                                                                                                   |
| 0x4     | MACRO_WRITE_BLANK_ERROR | This error is returned if a programming operation attempted to clear a bit that has previously been programmed to 1. The corresponding controller automatically recovers from this error when issuing a new command. Note however that the affected OTP word may be left in an inconsistent state if this error occurs. This can cause several issues when the word is accessed again (either as part of a regular read operation, as part of the readout at boot, or as part of a background check). It is important that SW ensures that each word is only written once, since this can render the device useless. |
| 0x5     | ACCESS_ERROR            | This error indicates that a locked memory region has been accessed. The corresponding controller automatically recovers from this error when issuing a new command.                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| 0x6     | CHECK_FAIL_ERROR        | An ECC, integrity or consistency mismatch has been detected in the buffer registers. This error should never occur during normal operation and is not recoverable. This error triggers an fatal_check_error alert.                                                                                                                                                                                                                                                                                                                                                                                                   |
| 0x7     | FSM_STATE_ERROR         | The FSM of the corresponding controller has reached an invalid state, or the FSM has been moved into a terminal error state due to an escalation action via lc_escalate_en_i. This error should never occur during normal operation and is not recoverable. If this error is present, this is a sign that the device has fallen victim to an invasive attack. This error triggers an fatal_check_error alert.                                                                                                                                                                                                        |


## DIRECT_ACCESS_REGWEN
Register write enable for all direct access interface registers.
- Offset: `0x5c`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "DIRECT_ACCESS_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                                                                |
|:------:|:------:|:-------:|:--------------------------------------------------------------------|
|  31:1  |        |         | Reserved                                                            |
|   0    |  rw0c  |   0x1   | [DIRECT_ACCESS_REGWEN](#direct_access_regwen--direct_access_regwen) |

### DIRECT_ACCESS_REGWEN . DIRECT_ACCESS_REGWEN
This bit controls whether the DAI registers can be written.
Write 0 to it in order to clear the bit.

Note that the hardware also modulates this bit and sets it to 0 temporarily
during an OTP operation such that the corresponding address and data registers
cannot be modified while an operation is pending. The [`DAI_IDLE`](#dai_idle) status bit
will also be set to 0 in such a case.

## DIRECT_ACCESS_CMD
Command register for direct accesses.
- Offset: `0x60`
- Reset default: `0x0`
- Reset mask: `0x7`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "RD", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"name": "WR", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"name": "DIGEST", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                                                                                                                |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:3  |        |         |        | Reserved                                                                                                                                                                                                                                                                                   |
|   2    | r0w1c  |   0x0   | DIGEST | Initiates the digest calculation and locking sequence for the partition specified by [`DIRECT_ACCESS_ADDRESS.`](#direct_access_address)                                                                                                                                                    |
|   1    | r0w1c  |   0x0   | WR     | Initiates a programming sequence that writes the data in [`DIRECT_ACCESS_WDATA_0`](#direct_access_wdata_0) and [`DIRECT_ACCESS_WDATA_1`](#direct_access_wdata_1) (for 64bit partitions) to the location specified by [`DIRECT_ACCESS_ADDRESS.`](#direct_access_address)                    |
|   0    | r0w1c  |   0x0   | RD     | Initiates a readout sequence that reads the location specified by [`DIRECT_ACCESS_ADDRESS.`](#direct_access_address) The command places the data read into [`DIRECT_ACCESS_RDATA_0`](#direct_access_rdata_0) and [`DIRECT_ACCESS_RDATA_1`](#direct_access_rdata_1) (for 64bit partitions). |

## DIRECT_ACCESS_ADDRESS
Address register for direct accesses.
- Offset: `0x64`
- Reset default: `0x0`
- Reset mask: `0xfff`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "DIRECT_ACCESS_ADDRESS", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                                   |
|:------:|:------:|:-------:|:-----------------------------------------------------------------------|
| 31:12  |        |         | Reserved                                                               |
|  11:0  |   rw   |   0x0   | [DIRECT_ACCESS_ADDRESS](#direct_access_address--direct_access_address) |

### DIRECT_ACCESS_ADDRESS . DIRECT_ACCESS_ADDRESS
This is the address for the OTP word to be read or written through
the direct access interface. Note that the address is aligned to the access size
internally, hence bits 1:0 are ignored for 32bit accesses, and bits 2:0 are ignored
for 64bit accesses.

For the digest calculation command, set this register to the partition base offset.

## DIRECT_ACCESS_WDATA
Write data for direct accesses.
Hardware automatically determines the access granule (32bit or 64bit) based on which
partition is being written to.
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Instances

| Name                  | Offset   |
|:----------------------|:---------|
| DIRECT_ACCESS_WDATA_0 | 0x68     |
| DIRECT_ACCESS_WDATA_1 | 0x6c     |


### Fields

```wavejson
{"reg": [{"name": "DIRECT_ACCESS_WDATA", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                | Description   |
|:------:|:------:|:-------:|:--------------------|:--------------|
|  31:0  |   rw   |   0x0   | DIRECT_ACCESS_WDATA |               |

## DIRECT_ACCESS_RDATA
Read data for direct accesses.
Hardware automatically determines the access granule (32bit or 64bit) based on which
partition is read from.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                  | Offset   |
|:----------------------|:---------|
| DIRECT_ACCESS_RDATA_0 | 0x70     |
| DIRECT_ACCESS_RDATA_1 | 0x74     |


### Fields

```wavejson
{"reg": [{"name": "DIRECT_ACCESS_RDATA", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                | Description   |
|:------:|:------:|:-------:|:--------------------|:--------------|
|  31:0  |   ro   |   0x0   | DIRECT_ACCESS_RDATA |               |

## CHECK_TRIGGER_REGWEN
Register write enable for [`CHECK_TRIGGER.`](#check_trigger)
- Offset: `0x78`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "CHECK_TRIGGER_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                                             |
|:------:|:------:|:-------:|:---------------------|:------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                      | Reserved                                                                                                                |
|   0    |  rw0c  |   0x1   | CHECK_TRIGGER_REGWEN | When cleared to 0, the [`CHECK_TRIGGER`](#check_trigger) register cannot be written anymore. Write 0 to clear this bit. |

## CHECK_TRIGGER
Command register for direct accesses.
- Offset: `0x7c`
- Reset default: `0x0`
- Reset mask: `0x3`
- Register enable: [`CHECK_TRIGGER_REGWEN`](#check_trigger_regwen)

### Fields

```wavejson
{"reg": [{"name": "INTEGRITY", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"name": "CONSISTENCY", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name                                       |
|:------:|:------:|:-------:|:-------------------------------------------|
|  31:2  |        |         | Reserved                                   |
|   1    | r0w1c  |   0x0   | [CONSISTENCY](#check_trigger--consistency) |
|   0    | r0w1c  |   0x0   | [INTEGRITY](#check_trigger--integrity)     |

### CHECK_TRIGGER . CONSISTENCY
Writing 1 to this bit triggers a consistency check. SW should monitor [`STATUS.CHECK_PENDING`](#status)
and wait until the check has been completed. If there are any errors, those will be flagged
in the [`STATUS`](#status) and [`ERR_CODE`](#err_code) registers, and via interrupts and alerts.

### CHECK_TRIGGER . INTEGRITY
Writing 1 to this bit triggers an integrity check. SW should monitor [`STATUS.CHECK_PENDING`](#status)
and wait until the check has been completed. If there are any errors, those will be flagged
in the [`STATUS`](#status) and [`ERR_CODE`](#err_code) registers, and via the interrupts and alerts.

## CHECK_REGWEN
Register write enable for [`INTEGRITY_CHECK_PERIOD`](#integrity_check_period) and [`CONSISTENCY_CHECK_PERIOD.`](#consistency_check_period)
- Offset: `0x80`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "CHECK_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                                                                                                                                                                        |
|:------:|:------:|:-------:|:-------------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |              | Reserved                                                                                                                                                                                           |
|   0    |  rw0c  |   0x1   | CHECK_REGWEN | When cleared to 0, [`INTEGRITY_CHECK_PERIOD`](#integrity_check_period) and [`CONSISTENCY_CHECK_PERIOD`](#consistency_check_period) registers cannot be written anymore. Write 0 to clear this bit. |

## CHECK_TIMEOUT
Timeout value for the integrity and consistency checks.
- Offset: `0x84`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CHECK_REGWEN`](#check_regwen)

### Fields

```wavejson
{"reg": [{"name": "CHECK_TIMEOUT", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                           |
|:------:|:------:|:-------:|:-----------------------------------------------|
|  31:0  |   rw   |   0x0   | [CHECK_TIMEOUT](#check_timeout--check_timeout) |

### CHECK_TIMEOUT . CHECK_TIMEOUT
Timeout value in cycles for the for the integrity and consistency checks. If an integrity or consistency
check does not complete within the timeout window, an error will be flagged in the [`STATUS`](#status) register,
an otp_error interrupt will be raised, and an fatal_check_error alert will be sent out. The timeout should
be set to a large value to stay on the safe side. The maximum check time can be upper bounded by the
number of cycles it takes to readout, scramble and digest the entire OTP array. Since this amounts to
roughly 25k cycles, it is recommended to set this value to at least 100'000 cycles in order to stay on the
safe side. A value of zero disables the timeout mechanism (default).

## INTEGRITY_CHECK_PERIOD
This value specifies the maximum period that can be generated pseudo-randomly.
Only applies to the HW_CFG* and SECRET* partitions once they are locked.
- Offset: `0x88`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CHECK_REGWEN`](#check_regwen)

### Fields

```wavejson
{"reg": [{"name": "INTEGRITY_CHECK_PERIOD", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                                      |
|:------:|:------:|:-------:|:--------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | [INTEGRITY_CHECK_PERIOD](#integrity_check_period--integrity_check_period) |

### INTEGRITY_CHECK_PERIOD . INTEGRITY_CHECK_PERIOD
The pseudo-random period is generated using a 40bit LFSR internally, and this register defines
the bit mask to be applied to the LFSR output in order to limit its range. The value of this
register is left shifted by 8bits and the lower bits are set to 8'hFF in order to form the 40bit mask.
A recommended value is 0x3_FFFF, corresponding to a maximum period of ~2.8s at 24MHz.
A value of zero disables the timer (default). Note that a one-off check can always be triggered via
[`CHECK_TRIGGER.INTEGRITY.`](#check_trigger)

## CONSISTENCY_CHECK_PERIOD
This value specifies the maximum period that can be generated pseudo-randomly.
This applies to the LIFE_CYCLE partition and the HW_CFG* and SECRET* partitions once they are locked.
- Offset: `0x8c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CHECK_REGWEN`](#check_regwen)

### Fields

```wavejson
{"reg": [{"name": "CONSISTENCY_CHECK_PERIOD", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                                            |
|:------:|:------:|:-------:|:--------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | [CONSISTENCY_CHECK_PERIOD](#consistency_check_period--consistency_check_period) |

### CONSISTENCY_CHECK_PERIOD . CONSISTENCY_CHECK_PERIOD
The pseudo-random period is generated using a 40bit LFSR internally, and this register defines
the bit mask to be applied to the LFSR output in order to limit its range. The value of this
register is left shifted by 8bits and the lower bits are set to 8'hFF in order to form the 40bit mask.
A recommended value is 0x3FF_FFFF, corresponding to a maximum period of ~716s at 24MHz.
A value of zero disables the timer (default). Note that a one-off check can always be triggered via
[`CHECK_TRIGGER.CONSISTENCY.`](#check_trigger)

## SW_MANUF_PARTITION_READ_LOCK
Runtime read lock for the SW_MANUF_PARTITION partition.
- Offset: `0x90`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "SW_MANUF_PARTITION_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 300}}
```

|  Bits  |  Type  |  Reset  | Name                         | Description                                                                                              |
|:------:|:------:|:-------:|:-----------------------------|:---------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                              | Reserved                                                                                                 |
|   0    |  rw0c  |   0x1   | SW_MANUF_PARTITION_READ_LOCK | When cleared to 0, read access to the SW_MANUF_PARTITION partition is locked. Write 0 to clear this bit. |

## SVN_PARTITION_READ_LOCK
Runtime read lock for the SVN_PARTITION partition.
- Offset: `0x94`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "SVN_PARTITION_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 250}}
```

|  Bits  |  Type  |  Reset  | Name                    | Description                                                                                         |
|:------:|:------:|:-------:|:------------------------|:----------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                         | Reserved                                                                                            |
|   0    |  rw0c  |   0x1   | SVN_PARTITION_READ_LOCK | When cleared to 0, read access to the SVN_PARTITION partition is locked. Write 0 to clear this bit. |

## VENDOR_TEST_PARTITION_READ_LOCK
Runtime read lock for the VENDOR_TEST_PARTITION partition.
- Offset: `0x98`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "VENDOR_TEST_PARTITION_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 330}}
```

|  Bits  |  Type  |  Reset  | Name                            | Description                                                                                                 |
|:------:|:------:|:-------:|:--------------------------------|:------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                                 | Reserved                                                                                                    |
|   0    |  rw0c  |   0x1   | VENDOR_TEST_PARTITION_READ_LOCK | When cleared to 0, read access to the VENDOR_TEST_PARTITION partition is locked. Write 0 to clear this bit. |

## VENDOR_HASHES_MANUF_PARTITION_READ_LOCK
Runtime read lock for the VENDOR_HASHES_MANUF_PARTITION partition.
- Offset: `0x9c`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "VENDOR_HASHES_MANUF_PARTITION_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 410}}
```

|  Bits  |  Type  |  Reset  | Name                                    | Description                                                                                                         |
|:------:|:------:|:-------:|:----------------------------------------|:--------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                                         | Reserved                                                                                                            |
|   0    |  rw0c  |   0x1   | VENDOR_HASHES_MANUF_PARTITION_READ_LOCK | When cleared to 0, read access to the VENDOR_HASHES_MANUF_PARTITION partition is locked. Write 0 to clear this bit. |

## VENDOR_HASHES_PROD_PARTITION_READ_LOCK
Runtime read lock for the VENDOR_HASHES_PROD_PARTITION partition.
- Offset: `0xa0`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "VENDOR_HASHES_PROD_PARTITION_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 400}}
```

|  Bits  |  Type  |  Reset  | Name                                   | Description                                                                                                        |
|:------:|:------:|:-------:|:---------------------------------------|:-------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                                        | Reserved                                                                                                           |
|   0    |  rw0c  |   0x1   | VENDOR_HASHES_PROD_PARTITION_READ_LOCK | When cleared to 0, read access to the VENDOR_HASHES_PROD_PARTITION partition is locked. Write 0 to clear this bit. |

## VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK
Runtime read lock for the VENDOR_REVOCATIONS_PROD_PARTITION partition.
- Offset: `0xa4`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 450}}
```

|  Bits  |  Type  |  Reset  | Name                                        | Description                                                                                                             |
|:------:|:------:|:-------:|:--------------------------------------------|:------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                                             | Reserved                                                                                                                |
|   0    |  rw0c  |   0x1   | VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK | When cleared to 0, read access to the VENDOR_REVOCATIONS_PROD_PARTITION partition is locked. Write 0 to clear this bit. |

## VENDOR_NON_SECRET_PROD_PARTITION_READ_LOCK
Runtime read lock for the VENDOR_NON_SECRET_PROD_PARTITION partition.
- Offset: `0xa8`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "VENDOR_NON_SECRET_PROD_PARTITION_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 440}}
```

|  Bits  |  Type  |  Reset  | Name                                       | Description                                                                                                            |
|:------:|:------:|:-------:|:-------------------------------------------|:-----------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                                            | Reserved                                                                                                               |
|   0    |  rw0c  |   0x1   | VENDOR_NON_SECRET_PROD_PARTITION_READ_LOCK | When cleared to 0, read access to the VENDOR_NON_SECRET_PROD_PARTITION partition is locked. Write 0 to clear this bit. |

## VENDOR_PK_HASH_VOLATILE_LOCK
Address register for direct accesses.
- Offset: `0xac`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "VENDOR_PK_HASH_VOLATILE_LOCK", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                         | Description                                       |
|:------:|:------:|:-------:|:-----------------------------|:--------------------------------------------------|
|  31:0  |   rw   |   0x0   | VENDOR_PK_HASH_VOLATILE_LOCK | Volatile write lock for vendor public key hashes. |

## SW_TEST_UNLOCK_PARTITION_DIGEST
Integrity digest for the SW_TEST_UNLOCK_PARTITION partition.
The integrity digest is 0 by default. The digest calculation can be triggered via the [`DIRECT_ACCESS_CMD.`](#direct_access_cmd)
After a reset, the digest then becomes visible in this CSR, and the corresponding partition becomes write-locked.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                              | Offset   |
|:----------------------------------|:---------|
| SW_TEST_UNLOCK_PARTITION_DIGEST_0 | 0xb0     |
| SW_TEST_UNLOCK_PARTITION_DIGEST_1 | 0xb4     |


### Fields

```wavejson
{"reg": [{"name": "SW_TEST_UNLOCK_PARTITION_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                            | Description   |
|:------:|:------:|:-------:|:--------------------------------|:--------------|
|  31:0  |   ro   |   0x0   | SW_TEST_UNLOCK_PARTITION_DIGEST |               |

## SECRET_MANUF_PARTITION_DIGEST
Integrity digest for the SECRET_MANUF_PARTITION partition.
The integrity digest is 0 by default. The digest calculation can be triggered via the [`DIRECT_ACCESS_CMD.`](#direct_access_cmd)
After a reset, the digest then becomes visible in this CSR, and the corresponding partition becomes write-locked.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                            | Offset   |
|:--------------------------------|:---------|
| SECRET_MANUF_PARTITION_DIGEST_0 | 0xb8     |
| SECRET_MANUF_PARTITION_DIGEST_1 | 0xbc     |


### Fields

```wavejson
{"reg": [{"name": "SECRET_MANUF_PARTITION_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                          | Description   |
|:------:|:------:|:-------:|:------------------------------|:--------------|
|  31:0  |   ro   |   0x0   | SECRET_MANUF_PARTITION_DIGEST |               |

## SECRET_PROD_PARTITION_0_DIGEST
Integrity digest for the SECRET_PROD_PARTITION_0 partition.
The integrity digest is 0 by default. The digest calculation can be triggered via the [`DIRECT_ACCESS_CMD.`](#direct_access_cmd)
After a reset, the digest then becomes visible in this CSR, and the corresponding partition becomes write-locked.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                             | Offset   |
|:---------------------------------|:---------|
| SECRET_PROD_PARTITION_0_DIGEST_0 | 0xc0     |
| SECRET_PROD_PARTITION_0_DIGEST_1 | 0xc4     |


### Fields

```wavejson
{"reg": [{"name": "SECRET_PROD_PARTITION_0_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                           | Description   |
|:------:|:------:|:-------:|:-------------------------------|:--------------|
|  31:0  |   ro   |   0x0   | SECRET_PROD_PARTITION_0_DIGEST |               |

## SECRET_PROD_PARTITION_1_DIGEST
Integrity digest for the SECRET_PROD_PARTITION_1 partition.
The integrity digest is 0 by default. The digest calculation can be triggered via the [`DIRECT_ACCESS_CMD.`](#direct_access_cmd)
After a reset, the digest then becomes visible in this CSR, and the corresponding partition becomes write-locked.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                             | Offset   |
|:---------------------------------|:---------|
| SECRET_PROD_PARTITION_1_DIGEST_0 | 0xc8     |
| SECRET_PROD_PARTITION_1_DIGEST_1 | 0xcc     |


### Fields

```wavejson
{"reg": [{"name": "SECRET_PROD_PARTITION_1_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                           | Description   |
|:------:|:------:|:-------:|:-------------------------------|:--------------|
|  31:0  |   ro   |   0x0   | SECRET_PROD_PARTITION_1_DIGEST |               |

## SECRET_PROD_PARTITION_2_DIGEST
Integrity digest for the SECRET_PROD_PARTITION_2 partition.
The integrity digest is 0 by default. The digest calculation can be triggered via the [`DIRECT_ACCESS_CMD.`](#direct_access_cmd)
After a reset, the digest then becomes visible in this CSR, and the corresponding partition becomes write-locked.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                             | Offset   |
|:---------------------------------|:---------|
| SECRET_PROD_PARTITION_2_DIGEST_0 | 0xd0     |
| SECRET_PROD_PARTITION_2_DIGEST_1 | 0xd4     |


### Fields

```wavejson
{"reg": [{"name": "SECRET_PROD_PARTITION_2_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                           | Description   |
|:------:|:------:|:-------:|:-------------------------------|:--------------|
|  31:0  |   ro   |   0x0   | SECRET_PROD_PARTITION_2_DIGEST |               |

## SECRET_PROD_PARTITION_3_DIGEST
Integrity digest for the SECRET_PROD_PARTITION_3 partition.
The integrity digest is 0 by default. The digest calculation can be triggered via the [`DIRECT_ACCESS_CMD.`](#direct_access_cmd)
After a reset, the digest then becomes visible in this CSR, and the corresponding partition becomes write-locked.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                             | Offset   |
|:---------------------------------|:---------|
| SECRET_PROD_PARTITION_3_DIGEST_0 | 0xd8     |
| SECRET_PROD_PARTITION_3_DIGEST_1 | 0xdc     |


### Fields

```wavejson
{"reg": [{"name": "SECRET_PROD_PARTITION_3_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                           | Description   |
|:------:|:------:|:-------:|:-------------------------------|:--------------|
|  31:0  |   ro   |   0x0   | SECRET_PROD_PARTITION_3_DIGEST |               |

## SW_MANUF_PARTITION_DIGEST
Integrity digest for the SW_MANUF_PARTITION partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the SW_MANUF_PARTITION partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                        | Offset   |
|:----------------------------|:---------|
| SW_MANUF_PARTITION_DIGEST_0 | 0xe0     |
| SW_MANUF_PARTITION_DIGEST_1 | 0xe4     |


### Fields

```wavejson
{"reg": [{"name": "SW_MANUF_PARTITION_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                      | Description   |
|:------:|:------:|:-------:|:--------------------------|:--------------|
|  31:0  |   ro   |   0x0   | SW_MANUF_PARTITION_DIGEST |               |

## SECRET_LC_TRANSITION_PARTITION_DIGEST
Integrity digest for the SECRET_LC_TRANSITION_PARTITION partition.
The integrity digest is 0 by default. The digest calculation can be triggered via the [`DIRECT_ACCESS_CMD.`](#direct_access_cmd)
After a reset, the digest then becomes visible in this CSR, and the corresponding partition becomes write-locked.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                                    | Offset   |
|:----------------------------------------|:---------|
| SECRET_LC_TRANSITION_PARTITION_DIGEST_0 | 0xe8     |
| SECRET_LC_TRANSITION_PARTITION_DIGEST_1 | 0xec     |


### Fields

```wavejson
{"reg": [{"name": "SECRET_LC_TRANSITION_PARTITION_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                  | Description   |
|:------:|:------:|:-------:|:--------------------------------------|:--------------|
|  31:0  |   ro   |   0x0   | SECRET_LC_TRANSITION_PARTITION_DIGEST |               |

## VENDOR_TEST_PARTITION_DIGEST
Integrity digest for the VENDOR_TEST_PARTITION partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the VENDOR_TEST_PARTITION partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                           | Offset   |
|:-------------------------------|:---------|
| VENDOR_TEST_PARTITION_DIGEST_0 | 0xf0     |
| VENDOR_TEST_PARTITION_DIGEST_1 | 0xf4     |


### Fields

```wavejson
{"reg": [{"name": "VENDOR_TEST_PARTITION_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                         | Description   |
|:------:|:------:|:-------:|:-----------------------------|:--------------|
|  31:0  |   ro   |   0x0   | VENDOR_TEST_PARTITION_DIGEST |               |

## VENDOR_HASHES_MANUF_PARTITION_DIGEST
Integrity digest for the VENDOR_HASHES_MANUF_PARTITION partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the VENDOR_HASHES_MANUF_PARTITION partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                                   | Offset   |
|:---------------------------------------|:---------|
| VENDOR_HASHES_MANUF_PARTITION_DIGEST_0 | 0xf8     |
| VENDOR_HASHES_MANUF_PARTITION_DIGEST_1 | 0xfc     |


### Fields

```wavejson
{"reg": [{"name": "VENDOR_HASHES_MANUF_PARTITION_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                 | Description   |
|:------:|:------:|:-------:|:-------------------------------------|:--------------|
|  31:0  |   ro   |   0x0   | VENDOR_HASHES_MANUF_PARTITION_DIGEST |               |

## VENDOR_HASHES_PROD_PARTITION_DIGEST
Integrity digest for the VENDOR_HASHES_PROD_PARTITION partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the VENDOR_HASHES_PROD_PARTITION partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                                  | Offset   |
|:--------------------------------------|:---------|
| VENDOR_HASHES_PROD_PARTITION_DIGEST_0 | 0x100    |
| VENDOR_HASHES_PROD_PARTITION_DIGEST_1 | 0x104    |


### Fields

```wavejson
{"reg": [{"name": "VENDOR_HASHES_PROD_PARTITION_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                | Description   |
|:------:|:------:|:-------:|:------------------------------------|:--------------|
|  31:0  |   ro   |   0x0   | VENDOR_HASHES_PROD_PARTITION_DIGEST |               |

## VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST
Integrity digest for the VENDOR_REVOCATIONS_PROD_PARTITION partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the VENDOR_REVOCATIONS_PROD_PARTITION partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                                       | Offset   |
|:-------------------------------------------|:---------|
| VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_0 | 0x108    |
| VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_1 | 0x10c    |


### Fields

```wavejson
{"reg": [{"name": "VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                     | Description   |
|:------:|:------:|:-------:|:-----------------------------------------|:--------------|
|  31:0  |   ro   |   0x0   | VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST |               |

## VENDOR_SECRET_PROD_PARTITION_DIGEST
Integrity digest for the VENDOR_SECRET_PROD_PARTITION partition.
The integrity digest is 0 by default. The digest calculation can be triggered via the [`DIRECT_ACCESS_CMD.`](#direct_access_cmd)
After a reset, the digest then becomes visible in this CSR, and the corresponding partition becomes write-locked.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                                  | Offset   |
|:--------------------------------------|:---------|
| VENDOR_SECRET_PROD_PARTITION_DIGEST_0 | 0x110    |
| VENDOR_SECRET_PROD_PARTITION_DIGEST_1 | 0x114    |


### Fields

```wavejson
{"reg": [{"name": "VENDOR_SECRET_PROD_PARTITION_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                | Description   |
|:------:|:------:|:-------:|:------------------------------------|:--------------|
|  31:0  |   ro   |   0x0   | VENDOR_SECRET_PROD_PARTITION_DIGEST |               |

## VENDOR_NON_SECRET_PROD_PARTITION_DIGEST
Integrity digest for the VENDOR_NON_SECRET_PROD_PARTITION partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the VENDOR_NON_SECRET_PROD_PARTITION partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                                      | Offset   |
|:------------------------------------------|:---------|
| VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_0 | 0x118    |
| VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_1 | 0x11c    |


### Fields

```wavejson
{"reg": [{"name": "VENDOR_NON_SECRET_PROD_PARTITION_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                    | Description   |
|:------:|:------:|:-------:|:----------------------------------------|:--------------|
|  31:0  |   ro   |   0x0   | VENDOR_NON_SECRET_PROD_PARTITION_DIGEST |               |

## SW_CFG_WINDOW
Any read to this window directly maps to the corresponding offset in the creator and owner software
config partitions, and triggers an OTP readout of the bytes requested. Note that the transaction
will block until OTP readout has completed.

- Word Aligned Offset Range: `0x1000`to`0x1ffc`
- Size (words): `1024`
- Access: `ro`
- Byte writes are *not* supported.

## Summary of the **`prim`** interface's registers

| Name                     | Offset   |   Length | Description   |
|:-------------------------|:---------|---------:|:--------------|
| otp_ctrl.[`CSR0`](#csr0) | 0x0      |        4 |               |
| otp_ctrl.[`CSR1`](#csr1) | 0x4      |        4 |               |
| otp_ctrl.[`CSR2`](#csr2) | 0x8      |        4 |               |
| otp_ctrl.[`CSR3`](#csr3) | 0xc      |        4 |               |
| otp_ctrl.[`CSR4`](#csr4) | 0x10     |        4 |               |
| otp_ctrl.[`CSR5`](#csr5) | 0x14     |        4 |               |
| otp_ctrl.[`CSR6`](#csr6) | 0x18     |        4 |               |
| otp_ctrl.[`CSR7`](#csr7) | 0x1c     |        4 |               |

## CSR0

- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x7ff3ff7`

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "field1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "field2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 1}, {"name": "field3", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 2}, {"name": "field4", "bits": 11, "attr": ["rw"], "rotate": 0}, {"bits": 5}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
| 31:27  |        |         |        | Reserved      |
| 26:16  |   rw   |   0x0   | field4 |               |
| 15:14  |        |         |        | Reserved      |
|  13:4  |   rw   |   0x0   | field3 |               |
|   3    |        |         |        | Reserved      |
|   2    |   rw   |   0x0   | field2 |               |
|   1    |   rw   |   0x0   | field1 |               |
|   0    |   rw   |   0x0   | field0 |               |

## CSR1

- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 7, "attr": ["rw"], "rotate": 0}, {"name": "field1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "field2", "bits": 7, "attr": ["rw"], "rotate": 0}, {"name": "field3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "field4", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
| 31:16  |   rw   |   0x0   | field4 |               |
|   15   |   rw   |   0x0   | field3 |               |
|  14:8  |   rw   |   0x0   | field2 |               |
|   7    |   rw   |   0x0   | field1 |               |
|  6:0   |   rw   |   0x0   | field0 |               |

## CSR2

- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:1  |        |         |        | Reserved      |
|   0    |   rw   |   0x0   | field0 |               |

## CSR3

- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0x7f3ff7`

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 3, "attr": ["rw1c"], "rotate": -90}, {"bits": 1}, {"name": "field1", "bits": 10, "attr": ["rw1c"], "rotate": 0}, {"bits": 2}, {"name": "field2", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "field3", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "field4", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "field5", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "field6", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "field7", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "field8", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 9}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
| 31:23  |        |         |        | Reserved      |
|   22   |   ro   |   0x0   | field8 |               |
|   21   |   ro   |   0x0   | field7 |               |
|   20   |   ro   |   0x0   | field6 |               |
|   19   |   ro   |   0x0   | field5 |               |
|   18   |   ro   |   0x0   | field4 |               |
|   17   |   ro   |   0x0   | field3 |               |
|   16   |  rw1c  |   0x0   | field2 |               |
| 15:14  |        |         |        | Reserved      |
|  13:4  |  rw1c  |   0x0   | field1 |               |
|   3    |        |         |        | Reserved      |
|  2:0   |  rw1c  |   0x0   | field0 |               |

## CSR4

- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0x73ff`

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 2}, {"name": "field1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "field2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "field3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 17}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
| 31:15  |        |         |        | Reserved      |
|   14   |   rw   |   0x0   | field3 |               |
|   13   |   rw   |   0x0   | field2 |               |
|   12   |   rw   |   0x0   | field1 |               |
| 11:10  |        |         |        | Reserved      |
|  9:0   |   rw   |   0x0   | field0 |               |

## CSR5

- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0xffff3fff`

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 6, "attr": ["rw"], "rotate": 0}, {"name": "field1", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "field2", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "field3", "bits": 3, "attr": ["ro"], "rotate": -90}, {"name": "field4", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "field5", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 2}, {"name": "field6", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
| 31:16  |   rw   |   0x0   | field6 |               |
| 15:14  |        |         |        | Reserved      |
|   13   |   ro   |   0x0   | field5 |               |
|   12   |   ro   |   0x0   | field4 |               |
|  11:9  |   ro   |   0x0   | field3 |               |
|   8    |   ro   |   0x0   | field2 |               |
|  7:6   |   rw   |   0x0   | field1 |               |
|  5:0   |   rw   |   0x0   | field0 |               |

## CSR6

- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0xffff1bff`

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 1}, {"name": "field1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "field2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 3}, {"name": "field3", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
| 31:16  |   rw   |   0x0   | field3 |               |
| 15:13  |        |         |        | Reserved      |
|   12   |   rw   |   0x0   | field2 |               |
|   11   |   rw   |   0x0   | field1 |               |
|   10   |        |         |        | Reserved      |
|  9:0   |   rw   |   0x0   | field0 |               |

## CSR7

- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0xc73f`

### Fields

```wavejson
{"reg": [{"name": "field0", "bits": 6, "attr": ["ro"], "rotate": 0}, {"bits": 2}, {"name": "field1", "bits": 3, "attr": ["ro"], "rotate": -90}, {"bits": 3}, {"name": "field2", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "field3", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
| 31:16  |        |         |        | Reserved      |
|   15   |   ro   |   0x0   | field3 |               |
|   14   |   ro   |   0x0   | field2 |               |
| 13:11  |        |         |        | Reserved      |
|  10:8  |   ro   |   0x0   | field1 |               |
|  7:6   |        |         |        | Reserved      |
|  5:0   |   ro   |   0x0   | field0 |               |

