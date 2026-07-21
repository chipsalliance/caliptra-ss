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

package caliptra_ss_usb_ocp_recovery_tb_pkg;

// This package is the verification-side source of OCP Recovery protocol
// definitions. Values are independently derived from OCP Recovery v1.1 and
// USB 2.0; the package intentionally has no dependency on DUT/RTL packages.

typedef logic [7:0] ocp_cmd_t;

// OCP Recovery v1.1 Section 9.2 command codes.
localparam ocp_cmd_t OCP_CMD_PROT_CAP             = 8'h22;
localparam ocp_cmd_t OCP_CMD_DEVICE_ID            = 8'h23;
localparam ocp_cmd_t OCP_CMD_DEVICE_STATUS        = 8'h24;
localparam ocp_cmd_t OCP_CMD_DEVICE_RESET         = 8'h25;
localparam ocp_cmd_t OCP_CMD_RECOVERY_CTRL        = 8'h26;
localparam ocp_cmd_t OCP_CMD_RECOVERY_STATUS      = 8'h27;
localparam ocp_cmd_t OCP_CMD_HW_STATUS            = 8'h28;
localparam ocp_cmd_t OCP_CMD_INDIRECT_CTRL        = 8'h29;
localparam ocp_cmd_t OCP_CMD_INDIRECT_STATUS      = 8'h2A;
localparam ocp_cmd_t OCP_CMD_INDIRECT_DATA        = 8'h2B;
localparam ocp_cmd_t OCP_CMD_VENDOR               = 8'h2C;
localparam ocp_cmd_t OCP_CMD_INDIRECT_FIFO_CTRL   = 8'h2D;
localparam ocp_cmd_t OCP_CMD_INDIRECT_FIFO_STATUS = 8'h2E;
localparam ocp_cmd_t OCP_CMD_INDIRECT_FIFO_DATA   = 8'h2F;
localparam ocp_cmd_t OCP_CMD_MIN                  = OCP_CMD_PROT_CAP;
localparam ocp_cmd_t OCP_CMD_MAX                  = OCP_CMD_INDIRECT_FIFO_DATA;

// Compatibility names used by the existing recovery sequence.
localparam ocp_cmd_t OCP_REC_CMD_PROT_CAP             = OCP_CMD_PROT_CAP;
localparam ocp_cmd_t OCP_REC_CMD_DEVICE_ID            = OCP_CMD_DEVICE_ID;
localparam ocp_cmd_t OCP_REC_CMD_DEVICE_STATUS        = OCP_CMD_DEVICE_STATUS;
localparam ocp_cmd_t OCP_REC_CMD_RESET                = OCP_CMD_DEVICE_RESET;
localparam ocp_cmd_t OCP_REC_CMD_RECOVERY_CTRL        = OCP_CMD_RECOVERY_CTRL;
localparam ocp_cmd_t OCP_REC_CMD_RECOVERY_STATUS      = OCP_CMD_RECOVERY_STATUS;
localparam ocp_cmd_t OCP_REC_CMD_HW_STATUS            = OCP_CMD_HW_STATUS;
localparam ocp_cmd_t OCP_REC_CMD_INDIRECT_CTRL        = OCP_CMD_INDIRECT_CTRL;
localparam ocp_cmd_t OCP_REC_CMD_INDIRECT_STATUS      = OCP_CMD_INDIRECT_STATUS;
localparam ocp_cmd_t OCP_REC_CMD_INDIRECT_DATA        = OCP_CMD_INDIRECT_DATA;
localparam ocp_cmd_t OCP_REC_CMD_VENDOR               = OCP_CMD_VENDOR;
localparam ocp_cmd_t OCP_REC_CMD_INDIRECT_FIFO_CTRL   = OCP_CMD_INDIRECT_FIFO_CTRL;
localparam ocp_cmd_t OCP_REC_CMD_INDIRECT_FIFO_STATUS = OCP_CMD_INDIRECT_FIFO_STATUS;
localparam ocp_cmd_t OCP_REC_CMD_INDIRECT_FIFO_DATA   = OCP_CMD_INDIRECT_FIFO_DATA;

// OCP Recovery v1.1 Section 9.2 payload bounds.
localparam int OCP_SPEC_LEN_PROT_CAP               = 15;
localparam int OCP_SPEC_MIN_LEN_DEVICE_ID          = 24;
localparam int OCP_SPEC_MAX_LEN_DEVICE_ID          = 255;
localparam int OCP_SPEC_MIN_LEN_DEVICE_STATUS      = 7;
localparam int OCP_SPEC_MAX_LEN_DEVICE_STATUS      = 255;
localparam int OCP_SPEC_LEN_DEVICE_RESET           = 3;
localparam int OCP_SPEC_LEN_RECOVERY_CTRL          = 3;
localparam int OCP_SPEC_LEN_RECOVERY_STATUS        = 2;
localparam int OCP_SPEC_MIN_LEN_HW_STATUS          = 4;
localparam int OCP_SPEC_MAX_LEN_HW_STATUS          = 255;
localparam int OCP_SPEC_LEN_INDIRECT_CTRL          = 6;
localparam int OCP_SPEC_LEN_INDIRECT_STATUS        = 6;
localparam int OCP_SPEC_MIN_LEN_INDIRECT_DATA      = 1;
localparam int OCP_SPEC_MIN_LEN_VENDOR             = 1;
localparam int OCP_SPEC_LEN_INDIRECT_FIFO_CTRL     = 6;
localparam int OCP_SPEC_LEN_INDIRECT_FIFO_STATUS   = 20;
localparam int OCP_SPEC_MIN_LEN_INDIRECT_FIFO_DATA = 1;

// PROT_CAP, OCP Recovery v1.1 Section 9.2.
localparam int OCP_OFF_PC_MAGIC_START       = 0;
localparam int OCP_OFF_PC_MAGIC_END         = 7;
localparam int OCP_OFF_PC_VERSION_MAJOR     = 8;
localparam int OCP_OFF_PC_VERSION_MINOR     = 9;
localparam int OCP_OFF_PC_AGENT_CAPS_LO     = 10;
localparam int OCP_OFF_PC_AGENT_CAPS_HI     = 11;
localparam int OCP_OFF_PC_CMS_COUNT         = 12;
localparam int OCP_OFF_PC_MAX_RESPONSE_TIME = 13;
localparam int OCP_OFF_PC_HEARTBEAT_PERIOD  = 14;

localparam logic [7:0] OCP_SPEC_PROT_CAP_MAGIC [0:7] = '{
    8'h4F, 8'h43, 8'h50, 8'h20, 8'h52, 8'h45, 8'h43, 8'h56
};
localparam logic [7:0] OCP_SPEC_VERSION_MAJOR = 8'h01;
localparam logic [7:0] OCP_SPEC_VERSION_MINOR = 8'h01;

localparam int OCP_CAP_IDENTIFICATION      = 0;
localparam int OCP_CAP_FORCED_RECOVERY     = 1;
localparam int OCP_CAP_MGMT_RESET          = 2;
localparam int OCP_CAP_DEVICE_RESET        = 3;
localparam int OCP_CAP_DEVICE_STATUS       = 4;
localparam int OCP_CAP_INDIRECT_CTRL       = 5;
localparam int OCP_CAP_LOCAL_C_IMAGE       = 6;
localparam int OCP_CAP_PUSH_C_IMAGE        = 7;
localparam int OCP_CAP_INTERFACE_ISOLATION = 8;
localparam int OCP_CAP_HW_STATUS           = 9;
localparam int OCP_CAP_VENDOR              = 10;
localparam int OCP_CAP_FLASHLESS_BOOT      = 11;
localparam int OCP_CAP_INDIRECT_FIFO       = 12;
localparam logic [15:0] OCP_CAP_RESERVED_MASK = 16'hE000;

// DEVICE_ID, OCP Recovery v1.1 Section 9.2.
localparam int OCP_OFF_DID_DESC_TYPE         = 0;
localparam int OCP_OFF_DID_VENDOR_STRING_LEN = 1;
localparam int OCP_OFF_DID_ID_START          = 2;
localparam int OCP_OFF_DID_VENDOR_STRING     = 24;

typedef enum logic [7:0] {
    OCP_DEVICE_ID_PCI_VENDOR      = 8'h00,
    OCP_DEVICE_ID_IANA            = 8'h01,
    OCP_DEVICE_ID_UUID            = 8'h02,
    OCP_DEVICE_ID_PNP_VENDOR      = 8'h03,
    OCP_DEVICE_ID_ACPI_VENDOR     = 8'h04,
    OCP_DEVICE_ID_IANA_ENTERPRISE = 8'h05,
    OCP_DEVICE_ID_NVME_MI         = 8'hFF
} tb_ocp_device_id_type_e;

// DEVICE_STATUS and protocol errors, OCP Recovery v1.1 Sections 9.1/9.2.
localparam int OCP_OFF_DS_STATUS        = 0;
localparam int OCP_OFF_DS_PROT_ERROR    = 1;
localparam int OCP_OFF_DS_REC_REASON_LO = 2;
localparam int OCP_OFF_DS_REC_REASON_HI = 3;
localparam int OCP_OFF_DS_HEARTBEAT_LO  = 4;
localparam int OCP_OFF_DS_HEARTBEAT_HI  = 5;
localparam int OCP_OFF_DS_VENDOR_LEN    = 6;
localparam int OCP_OFF_DS_VENDOR_START  = 7;

typedef enum logic [7:0] {
    OCP_DEVICE_STATUS_PENDING          = 8'h00,
    OCP_DEVICE_STATUS_HEALTHY          = 8'h01,
    OCP_DEVICE_STATUS_ERROR            = 8'h02,
    OCP_DEVICE_STATUS_RECOVERY_MODE    = 8'h03,
    OCP_DEVICE_STATUS_RECOVERY_PENDING = 8'h04,
    OCP_DEVICE_STATUS_RUNNING_RECOVERY = 8'h05,
    OCP_DEVICE_STATUS_BOOT_FAILURE     = 8'h0E,
    OCP_DEVICE_STATUS_FATAL_ERROR      = 8'h0F
} ocp_device_status_e;

typedef enum logic [7:0] {
    OCP_PROTOCOL_ERROR_NONE                  = 8'h00,
    OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND   = 8'h01,
    OCP_PROTOCOL_ERROR_UNSUPPORTED_PARAMETER = 8'h02,
    OCP_PROTOCOL_ERROR_LENGTH                = 8'h03,
    OCP_PROTOCOL_ERROR_CRC                   = 8'h04,
    OCP_PROTOCOL_ERROR_GENERAL               = 8'hFF
} ocp_protocol_error_e;

localparam int OCP_DEVICE_STATUS_HEARTBEAT_MAX  = 4095;
localparam int OCP_DEVICE_STATUS_VENDOR_LEN_MAX = 248;
localparam logic [15:0] OCP_REC_REASON_STANDARD_MAX = 16'h0012;
localparam logic [15:0] OCP_REC_REASON_VENDOR_MIN   = 16'h0080;
localparam logic [15:0] OCP_REC_REASON_VENDOR_MAX   = 16'h00FF;

// RECOVERY_STATUS, OCP Recovery v1.1 Section 9.2.
localparam int OCP_OFF_RS_STATUS_IMAGE_INDEX = 0;
localparam int OCP_OFF_RS_VENDOR_STATUS      = 1;
localparam logic [7:0] OCP_RS_STATUS_MASK       = 8'h0F;
localparam logic [7:0] OCP_RS_IMAGE_INDEX_MASK  = 8'hF0;
localparam int OCP_RS_IMAGE_INDEX_SHIFT         = 4;

typedef enum logic [3:0] {
    OCP_RECOVERY_STATUS_NOT_IN_RECOVERY = 4'h0,
    OCP_RECOVERY_STATUS_AWAITING_IMAGE  = 4'h1,
    OCP_RECOVERY_STATUS_BOOTING_IMAGE   = 4'h2,
    OCP_RECOVERY_STATUS_SUCCESS         = 4'h3,
    OCP_RECOVERY_STATUS_FAILED          = 4'hC,
    OCP_RECOVERY_STATUS_AUTH_ERROR      = 4'hD,
    OCP_RECOVERY_STATUS_ENTRY_ERROR     = 4'hE,
    OCP_RECOVERY_STATUS_INVALID_CMS     = 4'hF
} ocp_recovery_status_e;

// HW_STATUS, OCP Recovery v1.1 Section 9.2.
localparam int OCP_OFF_HW_DEV_STATUS    = 0;
localparam int OCP_OFF_HW_VENDOR_STATUS = 1;
localparam int OCP_OFF_HW_CTEMP         = 2;
localparam int OCP_OFF_HW_VENDOR_LEN    = 3;
localparam logic [7:0] OCP_HW_STATUS_RESERVED_MASK = 8'hF8;
localparam int OCP_HW_STATUS_VENDOR_LEN_MAX = 251;

// DEVICE_RESET and RECOVERY_CTRL, OCP Recovery v1.1 Section 9.2.
localparam int OCP_OFF_DR_RESET_CONTROL = 0;
localparam int OCP_OFF_DR_FORCED_RECOV  = 1;
localparam int OCP_OFF_DR_IFACE_CONTROL = 2;
localparam int OCP_OFF_RC_CMS           = 0;
localparam int OCP_OFF_RC_IMG_SEL       = 1;
localparam int OCP_OFF_RC_ACTIVATE      = 2;
localparam logic [7:0] OCP_RC_ACTIVATE_CODE = 8'h0F;

// INDIRECT_CTRL and INDIRECT_FIFO_CTRL, OCP Recovery v1.1 Section 9.2.
localparam int OCP_OFF_IC_CMS           = 0;
localparam int OCP_OFF_IC_RSVD          = 1;
localparam int OCP_OFF_IC_IMG_OFFSET_B0 = 2;
localparam int OCP_OFF_IC_IMG_OFFSET_B3 = 5;
localparam int OCP_OFF_IFC_CMS          = 0;
localparam int OCP_OFF_IFC_RESET        = 1;
localparam int OCP_OFF_IFC_IMG_SIZE_B0  = 2;
localparam int OCP_OFF_IFC_IMG_SIZE_B3  = 5;
localparam int OCP_IMG_UNIT_LOG2        = 2;

// INDIRECT_FIFO_STATUS, OCP Recovery v1.1 Section 9.2.
localparam int OCP_OFF_IFS_STATUS          = 0;
localparam int OCP_OFF_IFS_REGION_TYPE     = 1;
localparam int OCP_OFF_IFS_RESERVED_LO     = 2;
localparam int OCP_OFF_IFS_RESERVED_HI     = 3;
localparam int OCP_OFF_IFS_WRITE_INDEX_B0  = 4;
localparam int OCP_OFF_IFS_WRITE_INDEX_B3  = 7;
localparam int OCP_OFF_IFS_READ_INDEX_B0   = 8;
localparam int OCP_OFF_IFS_READ_INDEX_B3   = 11;
localparam int OCP_OFF_IFS_FIFO_SIZE_B0    = 12;
localparam int OCP_OFF_IFS_FIFO_SIZE_B3    = 15;
localparam int OCP_OFF_IFS_MAX_TRANSFER_B0 = 16;
localparam int OCP_OFF_IFS_MAX_TRANSFER_B3 = 19;
localparam logic [7:0] OCP_IFS_EMPTY_MASK      = 8'h01;
localparam logic [7:0] OCP_IFS_FULL_MASK       = 8'h02;
localparam logic [7:0] OCP_IFS_STATUS_RSVD_MASK = 8'hFC;

localparam logic [7:0] OCP_REGION_RECOVERY_CODE_WO = 8'h00;
localparam logic [7:0] OCP_REGION_DEBUG_LOG_RO     = 8'h01;
localparam logic [7:0] OCP_REGION_VENDOR_WO        = 8'h04;
localparam logic [7:0] OCP_REGION_VENDOR_RO        = 8'h05;
localparam logic [7:0] OCP_REGION_UNSUPPORTED      = 8'h07;

// OCP Recovery USB functional descriptor, OCP Recovery v1.1 Section 8.5.3.
localparam int OCP_USB_FUNC_DESC_LEN             = 10;
localparam logic [7:0] OCP_USB_FUNC_DESC_TYPE    = 8'h24;
localparam logic [7:0] OCP_USB_FUNC_DESC_SUBTYPE = 8'h01;
localparam int OCP_OFF_UFD_LENGTH         = 0;
localparam int OCP_OFF_UFD_TYPE           = 1;
localparam int OCP_OFF_UFD_SUBTYPE        = 2;
localparam int OCP_OFF_UFD_RESERVED       = 3;
localparam int OCP_OFF_UFD_MAX_WR_LO      = 4;
localparam int OCP_OFF_UFD_MAX_WR_HI      = 5;
localparam int OCP_OFF_UFD_MAX_RD_LO      = 6;
localparam int OCP_OFF_UFD_MAX_RD_HI      = 7;
localparam int OCP_OFF_UFD_BCD_VERSION_LO = 8;
localparam int OCP_OFF_UFD_BCD_VERSION_HI = 9;
localparam logic [15:0] OCP_USB_BCD_VERSION_1P1 = 16'h0110;
localparam int OCP_USB_MIN_TRANSFER_SIZE = 64;

// USB 2.0 Section 9.3 and OCP Recovery v1.1 Section 8.5.1.
localparam logic [1:0] BMRT_TYPE_CLASS      = 2'b01;
localparam logic [4:0] BMRT_RECIPIENT_IFACE = 5'b00001;
localparam logic [7:0] OCP_BREQUEST_XFER    = 8'h00;

// OCP Recovery v1.1 Section 8.2.5 RA FIFO flow-control options.
typedef enum logic [1:0] {
    FIFO_FLOW_BY_INDICES,
    FIFO_FLOW_BY_STATUS_FLAGS,
    FIFO_FLOW_BY_USB_NAK
} ocp_fifo_flow_control_strategy_e;

endpackage
