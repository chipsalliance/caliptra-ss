// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Coverage exclusion file for uart
// Format Version: 2
// ExclMode: default

//==================================================
// TL-UL Device Assertion Coverage Exclusions
//==================================================
INSTANCE: tb.dut.u_caliptra_ss_uart.tlul_assert_device.gen_device_cov
ANNOTATION: "[UNREACHABLE] sub2tlul enforces single outstanding txn; b2b requests unreachable"
Assert b2bReq_C "assertion"
ANNOTATION: "[UNREACHABLE] sub2tlul enforces single outstanding txn; b2b requests to same addr unreachable"
Assert b2bReqWithSameAddr_C "assertion"
ANNOTATION: "[ILLEGAL_PROTOCOL] sub2tlul is compliant; never drops a_valid before a_ready handshake"
Assert aValidNotAccepted_C "assertion"
ANNOTATION: "[ILLEGAL_PROTOCOL] sub2tlul is compliant; never changes address before a_ready handshake"
Assert a_addressChangedNotAccepted_C "assertion"
ANNOTATION: "[ILLEGAL_PROTOCOL] sub2tlul is compliant; never changes data before a_ready handshake"
Assert a_dataChangedNotAccepted_C "assertion"
ANNOTATION: "[ILLEGAL_PROTOCOL] sub2tlul is compliant; never changes opcode before a_ready handshake"
Assert a_opcodeChangedNotAccepted_C "assertion"
ANNOTATION: "[ILLEGAL_PROTOCOL] sub2tlul is compliant; never changes size before a_ready handshake"
Assert a_sizeChangedNotAccepted_C "assertion"
ANNOTATION: "[ILLEGAL_PROTOCOL] sub2tlul is compliant; never changes source before a_ready handshake"
Assert a_sourceChangedNotAccepted_C "assertion"
ANNOTATION: "[ILLEGAL_PROTOCOL] sub2tlul is compliant; never changes mask before a_ready handshake"
Assert a_maskChangedNotAccepted_C "assertion"
