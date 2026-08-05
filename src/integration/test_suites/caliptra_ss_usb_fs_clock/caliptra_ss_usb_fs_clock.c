//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
//
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
// Description: USB Full-Speed clock test for the Caliptra Subsystem.
//
//  This test verifies that the USB clock path is active and toggling after
//  the USB device controller is brought up. The USB reference clock is
//  generated inside the AST (src/ast/rtl/usb_clk.sv, usb_osc.sv ->
//  clk_src_usb_o) and feeds the USB controller's utmi_clk. Firmware brings
//  the USB device controller up via the standard boot_usb_core() and idles
//  so that the clock path stays active; frequency checking is done by a
//  TB-bound SystemVerilog checker (caliptra_ss_usb_fs_clock_checker.sv)
//  bound to the AST clk_src_usb_o net.
//
//  IMPORTANT - Full-speed selection:
//  The USB device controller DOES NOT provide a software "force full speed"
//  control bit in DEVCMDSTAT. DEVCMDSTAT.SPEED ([23:22], mask 0xC00000) is
//  READ-ONLY status; it reports the negotiated speed and cannot be written
//  to force FS. Full-speed operation must be selected on the PHY/link side:
//    - Set high_speed_capable=0 in the UVM host cfg (caliptra_ss_usb_shared_cfg)
//      so the VIP remote-device model does not offer HS chirp; OR
//    - Force UTMI xcvrselect/termselect/opmode to FS values in the TB.
//  This firmware does not (and cannot) override the negotiated speed; it only
//  brings the device controller up with standard defaults and then idles so
//  the USB clock path stays active for the TB checker.
//
//  Boot order: boot MCU -> bring USB device controller up -> bring up Caliptra
//  core -> idle so the USB clock keeps toggling for the TB checker window.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Number of idle poll iterations to keep the USB clock toggling so the TB
// frequency checker has a stable observation window.
#define USB_FS_IDLE_ITERS 20000

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif


void main (void) {

    uint32_t reg_data;

    VPRINTF(LOW, "=================\nMCU: USB FS clock test\n=================\n\n");

    // Standard MCU boot sequence.
    boot_mcu();

    // Bring the USB device controller up using the standard shared bring-up
    // function. Full-speed operation is selected by the PHY/VIP configuration,
    // not by a firmware register write (DEVCMDSTAT.SPEED is read-only status).
    boot_usb_core();

    // Caliptra core bringup.
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra core ready, USB clock active. Idling for checker.\n");

    reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT = 0x%x\n", reg_data);
    // SPEED is read-only status; log the negotiated speed for diagnostic use.
    VPRINTF(LOW, "MCU: USB negotiated SPEED field = 0x%x\n",
            (reg_data & USBHSD_DEVCMDSTAT_SPEED_MASK) >> USBHSD_DEVCMDSTAT_SPEED_LOW);
    reg_data = lsu_read_32(SOC_USBHSD_INFO);
    VPRINTF(LOW, "MCU: USB INFO = 0x%x\n", reg_data);

    // Idle loop: keep the device enabled while the TB frequency checker
    // observes clk_src_usb_o. Also service any bus reset so the link does not
    // drop out during the observation window.
    for (uint32_t i = 0; i < USB_FS_IDLE_ITERS; i++) {
        usb_handle_bus_reset();
    }

    reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT final = 0x%x\n", reg_data);
    VPRINTF(LOW, "MCU: USB FS clock test - halting\n");
    csr_write_mpmc_halt();
}
