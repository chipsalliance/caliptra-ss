// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
#ifndef CALIPTRA_SS_LC_CTRL_ADDRMAP_HEADER
#define CALIPTRA_SS_LC_CTRL_ADDRMAP_HEADER

#define CALIPTRA_SS_LC_CTRL_OFFSET 0x70000000
#define CALIPTRA_SS_LC_CTRL_READY_MASK 1
#define CALIPTRA_SS_LC_CTRL_INIT_MASK 3

#define LC_CTRL_ALERT_TEST_OFFSET                 (CALIPTRA_SS_LC_CTRL_OFFSET + 0x0 )
#define LC_CTRL_STATUS_OFFSET                     (CALIPTRA_SS_LC_CTRL_OFFSET + 0x4 )
#define LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_OFFSET (CALIPTRA_SS_LC_CTRL_OFFSET + 0x8 )
#define LC_CTRL_CLAIM_TRANSITION_IF_OFFSET        (CALIPTRA_SS_LC_CTRL_OFFSET + 0xc )
#define LC_CTRL_TRANSITION_REGWEN_OFFSET          (CALIPTRA_SS_LC_CTRL_OFFSET + 0x10)
#define LC_CTRL_TRANSITION_CMD_OFFSET             (CALIPTRA_SS_LC_CTRL_OFFSET + 0x14)
#define LC_CTRL_TRANSITION_CTRL_OFFSET            (CALIPTRA_SS_LC_CTRL_OFFSET + 0x18)
#define LC_CTRL_TRANSITION_TOKEN_0_OFFSET         (CALIPTRA_SS_LC_CTRL_OFFSET + 0x1c)
#define LC_CTRL_TRANSITION_TOKEN_1_OFFSET         (CALIPTRA_SS_LC_CTRL_OFFSET + 0x20)
#define LC_CTRL_TRANSITION_TOKEN_2_OFFSET         (CALIPTRA_SS_LC_CTRL_OFFSET + 0x24)
#define LC_CTRL_TRANSITION_TOKEN_3_OFFSET         (CALIPTRA_SS_LC_CTRL_OFFSET + 0x28)
#define LC_CTRL_TRANSITION_TARGET_OFFSET          (CALIPTRA_SS_LC_CTRL_OFFSET + 0x2c)
#define LC_CTRL_OTP_VENDOR_TEST_CTRL_OFFSET       (CALIPTRA_SS_LC_CTRL_OFFSET + 0x30)
#define LC_CTRL_OTP_VENDOR_TEST_STATUS_OFFSET     (CALIPTRA_SS_LC_CTRL_OFFSET + 0x34)
#define LC_CTRL_LC_STATE_OFFSET                   (CALIPTRA_SS_LC_CTRL_OFFSET + 0x38)
#define LC_CTRL_LC_TRANSITION_CNT_OFFSET          (CALIPTRA_SS_LC_CTRL_OFFSET + 0x3c)
#define LC_CTRL_LC_ID_STATE_OFFSET                (CALIPTRA_SS_LC_CTRL_OFFSET + 0x40)
#define LC_CTRL_HW_REVISION0_OFFSET               (CALIPTRA_SS_LC_CTRL_OFFSET + 0x44)
#define LC_CTRL_HW_REVISION1_OFFSET               (CALIPTRA_SS_LC_CTRL_OFFSET + 0x48)
#define LC_CTRL_DEVICE_ID_0_OFFSET                (CALIPTRA_SS_LC_CTRL_OFFSET + 0x4c)
#define LC_CTRL_DEVICE_ID_1_OFFSET                (CALIPTRA_SS_LC_CTRL_OFFSET + 0x50)
#define LC_CTRL_DEVICE_ID_2_OFFSET                (CALIPTRA_SS_LC_CTRL_OFFSET + 0x54)
#define LC_CTRL_DEVICE_ID_3_OFFSET                (CALIPTRA_SS_LC_CTRL_OFFSET + 0x58)
#define LC_CTRL_DEVICE_ID_4_OFFSET                (CALIPTRA_SS_LC_CTRL_OFFSET + 0x5c)
#define LC_CTRL_DEVICE_ID_5_OFFSET                (CALIPTRA_SS_LC_CTRL_OFFSET + 0x60)
#define LC_CTRL_DEVICE_ID_6_OFFSET                (CALIPTRA_SS_LC_CTRL_OFFSET + 0x64)
#define LC_CTRL_DEVICE_ID_7_OFFSET                (CALIPTRA_SS_LC_CTRL_OFFSET + 0x68)
#define LC_CTRL_MANUF_STATE_0_OFFSET              (CALIPTRA_SS_LC_CTRL_OFFSET + 0x6c)
#define LC_CTRL_MANUF_STATE_1_OFFSET              (CALIPTRA_SS_LC_CTRL_OFFSET + 0x70)
#define LC_CTRL_MANUF_STATE_2_OFFSET              (CALIPTRA_SS_LC_CTRL_OFFSET + 0x74)
#define LC_CTRL_MANUF_STATE_3_OFFSET              (CALIPTRA_SS_LC_CTRL_OFFSET + 0x78)
#define LC_CTRL_MANUF_STATE_4_OFFSET              (CALIPTRA_SS_LC_CTRL_OFFSET + 0x7c)
#define LC_CTRL_MANUF_STATE_5_OFFSET              (CALIPTRA_SS_LC_CTRL_OFFSET + 0x80)
#define LC_CTRL_MANUF_STATE_6_OFFSET              (CALIPTRA_SS_LC_CTRL_OFFSET + 0x84)
#define LC_CTRL_MANUF_STATE_7_OFFSET              (CALIPTRA_SS_LC_CTRL_OFFSET + 0x88)



#define CALIPTRA_SS_LC_CTRL_REGISTERS {     LC_CTRL_ALERT_TEST_OFFSET, \
                                            LC_CTRL_STATUS_OFFSET, \
                                            LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_OFFSET, \
                                            LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, \
                                            LC_CTRL_TRANSITION_REGWEN_OFFSET, \
                                            LC_CTRL_TRANSITION_CMD_OFFSET, \
                                            LC_CTRL_TRANSITION_CTRL_OFFSET, \
                                            LC_CTRL_TRANSITION_TOKEN_0_OFFSET, \
                                            LC_CTRL_TRANSITION_TOKEN_1_OFFSET, \
                                            LC_CTRL_TRANSITION_TOKEN_2_OFFSET, \
                                            LC_CTRL_TRANSITION_TOKEN_3_OFFSET, \
                                            LC_CTRL_TRANSITION_TARGET_OFFSET, \
                                            LC_CTRL_OTP_VENDOR_TEST_CTRL_OFFSET, \
                                            LC_CTRL_OTP_VENDOR_TEST_STATUS_OFFSET, \
                                            LC_CTRL_LC_STATE_OFFSET, \
                                            LC_CTRL_LC_TRANSITION_CNT_OFFSET, \
                                            LC_CTRL_LC_ID_STATE_OFFSET, \
                                            LC_CTRL_HW_REVISION0_OFFSET, \
                                            LC_CTRL_HW_REVISION1_OFFSET, \
                                            LC_CTRL_DEVICE_ID_0_OFFSET, \
                                            LC_CTRL_DEVICE_ID_1_OFFSET, \
                                            LC_CTRL_DEVICE_ID_2_OFFSET, \
                                            LC_CTRL_DEVICE_ID_3_OFFSET, \
                                            LC_CTRL_DEVICE_ID_4_OFFSET, \
                                            LC_CTRL_DEVICE_ID_5_OFFSET, \
                                            LC_CTRL_DEVICE_ID_6_OFFSET, \
                                            LC_CTRL_DEVICE_ID_7_OFFSET, \
                                            LC_CTRL_MANUF_STATE_0_OFFSET, \
                                            LC_CTRL_MANUF_STATE_1_OFFSET, \
                                            LC_CTRL_MANUF_STATE_2_OFFSET, \
                                            LC_CTRL_MANUF_STATE_3_OFFSET, \
                                            LC_CTRL_MANUF_STATE_4_OFFSET, \
                                            LC_CTRL_MANUF_STATE_5_OFFSET, \
                                            LC_CTRL_MANUF_STATE_6_OFFSET, \
                                            LC_CTRL_MANUF_STATE_7_OFFSET }
#endif
