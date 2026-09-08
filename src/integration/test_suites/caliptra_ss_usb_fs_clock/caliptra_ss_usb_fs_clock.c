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
// Description: USB Full-Speed link test for the Caliptra Subsystem.
//
//  This test brings the USB device controller up in Full-Speed-only mode
//  behind the compound hub and keeps it alive long enough for the testbench
//  checker to prove that the link is actually running at Full Speed.
//
//  Speed observation:
//  There is no USB clock whose frequency encodes the link speed in this
//  testbench. The AST clock generators (src/ast/rtl/usb_clk.sv, usb_osc.sv,
//  clk_src_usb_o) are NOT compiled into caliptra_ss_top_tb, and the UTMI
//  clock rate is the same for HS and FS. USB speed is carried by the
//  protocol and by the PHY speed-select pins, not by a clock rate. The link
//  speed is therefore checked by caliptra_ss_usb_fs_speed_checker.sv, which
//  observes the UTMI interface directly: it requires xcvrselect/termselect
//  to be at their FS values and measures the RXValid byte period in
//  simulation time (about 666.7 ns at 12 Mbit/s versus 16.7 ns at
//  480 Mbit/s). The byte period is measured as elapsed time rather than as a
//  count of UTMI clocks on purpose, because the UTMI clock frequency at that
//  interface is VIP-generated and is not the 60 MHz the testbench defines for
//  its own usb_utmi_clk. It is enabled by the +usb_fs_speed_check plusarg
//  from this test's .yml descriptor.

//
//  Full-speed selection:
//  DEVCMDSTAT.SPEED ([23:22], mask 0xC00000) is READ-ONLY status and cannot
//  be written to force FS. FS is selected on two sides:
//    - The UVM test sets high_speed_capable=0 in the host cfg, so the VIP
//      never offers HS chirp.
//    - Firmware calls boot_usb_core_fs(), which sets DEVCMDSTAT.PFSC (Port
//      Force Full Speed Connect) so the device controller does not emit
//      K-chirp and does not stall ~2.2 ms waiting for a J-chirp reply that
//      an FS-only host never sends.
//
//  Boot order: boot MCU -> boot USB device controller FS (which also does
//  hub bring-up phase 1: HUB RAM + HUB_EN) -> usb_hub_connect() (phase 2:
//  HUB_CONNECT, now that USBDC0 is programmed) -> bring up Caliptra core ->
//  idle so the link stays up for the checker's observation window.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Number of idle poll iterations to keep the link up so the TB speed checker
// has a stable observation window. The checker only needs a handful of
// received bytes, so this is kept short to save simulation time.
#define USB_FS_IDLE_ITERS 4000

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

    // Bring the USB device controller up in FS-only mode. boot_usb_core_fs()
    // sets DEVCMDSTAT.PFSC to suppress the device-side K-chirp, and performs
    // hub bring-up phase 1 (HUB RAM programming + HUB_EN) before programming
    // USBDC0. Do not use boot_usb_core() here: it leaves the device HS-capable
    // and the chirp FSM would stall waiting for a J-chirp reply that the
    // FS-only host VIP never drives.
    boot_usb_core_fs();

    // Hub bring-up phase 2: assert HUB_CONNECT now that USBDC0 is fully
    // programmed, so the upstream host can see the hub and enumerate the
    // embedded device. Without this the host never sees anything on the bus.
    usb_hub_connect();

    // Caliptra core bringup.
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra core ready, USB link up. Idling for checker.\n");

    reg_data = lsu_read_32(USB_DEV0_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT = 0x%x\n", reg_data);
    // SPEED is read-only status; log the negotiated speed for diagnostic use.
    VPRINTF(LOW, "MCU: USB negotiated SPEED field = 0x%x\n",
            (reg_data & USBHSD_DEVCMDSTAT_SPEED_MASK) >> USBHSD_DEVCMDSTAT_SPEED_LOW);
    reg_data = lsu_read_32(USB_DEV0_INFO);
    VPRINTF(LOW, "MCU: USB INFO = 0x%x\n", reg_data);

    // Idle loop: keep the device enabled while the TB speed checker observes
    // the UTMI interface. Also service any bus reset so the link does not drop
    // out during the observation window.
    for (uint32_t i = 0; i < USB_FS_IDLE_ITERS; i++) {
        usb_handle_bus_reset();
    }

    reg_data = lsu_read_32(USB_DEV0_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT final = 0x%x\n", reg_data);
    VPRINTF(LOW, "MCU: USB FS clock test - halting\n");
    csr_write_mpmc_halt();
}
