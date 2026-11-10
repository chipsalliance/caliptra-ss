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
// Bench-specific probe that instantiates usb_hub_cov for caliptra_ss_top_tb.
//
// WHY THIS FILE EXISTS
// --------------------
// usb_hub_cov observes signals that live inside the VHDL architecture of the
// compound IP, and a SystemVerilog bind cannot target a VHDL entity. The
// coverage model therefore stays bench-independent in src/usb/coverage and all
// of the hierarchy strings are collected here, in the same style as
// usb_dev_addr_probe.sv. A usb_top_tb equivalent can drive the identical port
// list from its own path, so the covergroup and bin names match in both
// benches and URG can merge the two coverage databases.
//
// SIGNAL SELECTION RULE
// ---------------------
// Every reference below targets a PORT of a VHDL sub-instance, never a signal
// declared in the compound architecture itself, because only port-mapped nets
// are reliably registered for VCS cross-module reference in a mixed-language
// build. Where the coverage model wants a compound-level architecture signal,
// the equivalent sub-instance port that the signal is mapped onto is probed
// instead. Those substitutions are called out individually below.
//
// The whole file is guarded by USB_FCOV so a build without the define carries
// no coverage instrumentation.
module usb_cov_probe_caliptra_ss;

`ifdef USB_FCOV

  // Hub descriptor/control block. hub_enable and hub_dcon are the compound's
  // hub_enable_q / hub_dcon_q nets seen on the ports they are mapped to.
  localparam int unsigned HUB_PORTS = 2;

  logic       clk;
  logic       rst_n;

  logic       hub_enable;
  logic       hub_dcon;
  logic       hub_force_vbus;
  logic       hub_lpm_sup;
  logic       hub_force_fs;
  logic       hub_pll_on;
  logic       hub_vbusdebounced;
  logic [1:0] pie_speed;
  logic       usb_self_powered_ff;

  logic       reg_write;
  logic [7:0] reg_waddr;

  // Declared here rather than with the per-device block below because
  // u_usb_hub_cov consumes d0_phy_test_mode and must see the declaration
  // first. The assignments stay with the other usb_reg_if reads.
  logic [2:0] d0_phy_test_mode, d1_phy_test_mode;

  logic [1:0] pie_dev_selected;
  logic       dma_ahb_selected;

  logic       deviceenabled_hub;
  logic       deviceenabled_dev0;
  logic       deviceenabled_dev1;

  logic [HUB_PORTS-1:0] hub_port_connect;
  logic [HUB_PORTS-1:0] hub_port_enable;
  logic [HUB_PORTS-1:0] hub_port_suspend;
  logic [HUB_PORTS-1:0] hub_port_reset;
  logic [HUB_PORTS-1:0] hub_port_l1;
  logic [HUB_PORTS-1:0] hub_port_remotewakeup;

  logic        hub_epin_enable_buffer;
  logic        hub_epin_stall;

  logic        ep0_setupdone;
  logic [6:0]  ep0_request;
  logic [15:0] ep0_wvalue;
  logic [15:0] ep0_windex;
  logic        ep0_class_stall;

  logic        sync_suspend;
  logic        sync_busreset;
  logic        ep0_remote_wake_enabled_hub;
  logic        hub_remotewakeup;

  // ---------------------------------------------------------------------------
  // Clock and reset
  // ---------------------------------------------------------------------------
  // The compound runs on the AXI clock domain, which the wrapper forwards to
  // the IP as hclk / hresetn.
  always_comb clk   = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.usb_axi_aclk;
  always_comb rst_n = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.usb_axi_aresetn;

  // ---------------------------------------------------------------------------
  // Hub control register block (usb_ep0_hub_descr ports)
  // ---------------------------------------------------------------------------
  always_comb hub_enable          = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_ep0_hub_descr_1.hub_enable;
  always_comb hub_dcon            = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_ep0_hub_descr_1.hub_dcon;
  always_comb hub_force_vbus      = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_ep0_hub_descr_1.hub_force_vbus;
  always_comb hub_lpm_sup         = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_ep0_hub_descr_1.hub_lpm_sup;
  always_comb hub_force_fs        = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_ep0_hub_descr_1.hub_force_fs;
  always_comb hub_pll_on          = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_ep0_hub_descr_1.hub_pll_on;
  always_comb hub_vbusdebounced   = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_ep0_hub_descr_1.hub_vbusdebounced;
  always_comb pie_speed           = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_ep0_hub_descr_1.pie_speed;
  always_comb usb_self_powered_ff = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_ep0_hub_descr_1.usb_self_powered_ff;

  // Table write port. reg_waddr is log2(C_NWORDS) = 8 bits wide for the
  // default C_NWORDS of 196.
  always_comb reg_write = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_ep0_hub_descr_1.reg_write;
  always_comb reg_waddr = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_ep0_hub_descr_1.reg_waddr;

  // ---------------------------------------------------------------------------
  // Compound function multiplexing
  // ---------------------------------------------------------------------------
  // The compound's own pie_dev_selected is a VHDL integer, which is awkward to
  // bridge. The OCP recovery arbiter receives the same selection already
  // converted to a 2-bit std_logic_vector on its pie_dev_selected_i port, so
  // that port is probed instead. Note this is the SYNCHRONIZED selection
  // (sync_pie_dev_selected), which is the one the DMA context actually follows.
  always_comb pie_dev_selected = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_ocp_recovery_post_sync_arb_1.pie_dev_selected_i;

  // The compound's dma_ahb_selected is not reachable by cross-module
  // reference: usb_dma_1 sits inside an unnamed generate block, which VCS
  // refuses to resolve (XMRE). The compound structure derives the net as
  //   dma_ahb_selected <= '1' when sync_pie_dev_selected >= C_NBDEV else '0'
  // so the same expression is reproduced here from the synchronized selection
  // probed above. C_NBDEV is 1 in this configuration.
  localparam int unsigned NUM_HW_DEVICES = 1;

  always_comb dma_ahb_selected = (pie_dev_selected >= NUM_HW_DEVICES);

  // Device-enable legs. usbreg_deviceenabled is one vector on the PIE port,
  // indexed hub, dev0, dev1.
  always_comb deviceenabled_hub  = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.usbreg_deviceenabled[0];
  always_comb deviceenabled_dev0 = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.usbreg_deviceenabled[1];
  always_comb deviceenabled_dev1 = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.usbreg_deviceenabled[2];

  // ---------------------------------------------------------------------------
  // Downstream port state and class request dispatch (usb_app_hw_hub ports)
  // ---------------------------------------------------------------------------
  always_comb hub_port_connect      = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_app_hw_hub_1.hub_port_connect;
  always_comb hub_port_enable       = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_app_hw_hub_1.hub_port_enable;
  always_comb hub_port_suspend      = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_app_hw_hub_1.hub_port_suspend;
  always_comb hub_port_reset        = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_app_hw_hub_1.hub_port_reset;
  always_comb hub_port_l1           = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_app_hw_hub_1.hub_port_l1;
  always_comb hub_port_remotewakeup = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_app_hw_hub_1.hub_port_remotewakeup;

  always_comb hub_epin_enable_buffer = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_app_hw_hub_1.hub_epin_enable_buffer;
  always_comb hub_epin_stall         = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_app_hw_hub_1.hub_epin_stall;

  // Taken from the hub application block rather than the EP0 handler, because
  // the handler drives these as per-device vectors while the hub block sees
  // the already-selected scalar for the hub function.
  always_comb ep0_setupdone   = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_app_hw_hub_1.ep0_setupdone;
  always_comb ep0_request     = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_app_hw_hub_1.ep0_request;
  always_comb ep0_wvalue      = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_app_hw_hub_1.ep0_wvalue;
  always_comb ep0_windex      = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_app_hw_hub_1.ep0_windex;
  always_comb ep0_class_stall = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_app_hw_hub_1.ep0_class_stall;

  // ---------------------------------------------------------------------------
  // Remote wakeup gate terms
  // ---------------------------------------------------------------------------
  // sync_suspend is read from the synchronizer output port that produces it;
  // sync_busreset is read from the hub block input port that consumes it.
  always_comb sync_suspend  = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_synchronizer_1.sync_suspend;
  always_comb sync_busreset = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_app_hw_hub_1.sync_busreset;

  // The EP0 handler drives this as a per-device vector; the hub is device 0.
  always_comb ep0_remote_wake_enabled_hub = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_ep0_handler_1.ep0_remote_wake_enabled[0];

  // CAVEAT: the compound's hub_remotewakeup is an architecture signal with no
  // port of its own. usbreg_remotewakeup on the PIE carries it unchanged while
  // hub mode is active ("usbreg_remotewakeup <= hub_remotewakeup when
  // hub_enable_q = '1' else hub_port_remotewakeup(0)"), so this probe is exact
  // in hub mode and reports the bypass-mode device request otherwise. The
  // wakeup-gate coverage is only meaningful in hub mode, so that is acceptable.
  always_comb hub_remotewakeup = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.usbreg_remotewakeup;

  // ---------------------------------------------------------------------------
  // Coverage model instance
  // ---------------------------------------------------------------------------
  usb_hub_cov #(
    .HUB_PORTS      (HUB_PORTS),
    .HUB_WORDS      (196)
  ) u_usb_hub_cov (
    .clk                        (clk),
    .rst_n                      (rst_n),

    .hub_enable                 (hub_enable),
    .hub_dcon                   (hub_dcon),
    .hub_force_vbus             (hub_force_vbus),
    .hub_lpm_sup                (hub_lpm_sup),
    .hub_force_fs               (hub_force_fs),
    .hub_pll_on                 (hub_pll_on),
    .hub_vbusdebounced          (hub_vbusdebounced),
    .pie_speed                  (pie_speed),
    .usb_self_powered_ff        (usb_self_powered_ff),

    .reg_write                  (reg_write),
    .reg_waddr                  (reg_waddr),

    .phy_test_mode              (d0_phy_test_mode),

    .hub_port_connect           (hub_port_connect),
    .hub_port_enable            (hub_port_enable),
    .hub_port_suspend           (hub_port_suspend),
    .hub_port_reset             (hub_port_reset),
    .hub_port_l1                (hub_port_l1),
    .hub_port_remotewakeup      (hub_port_remotewakeup),

    .hub_epin_enable_buffer     (hub_epin_enable_buffer),
    .hub_epin_stall             (hub_epin_stall),

    .ep0_setupdone              (ep0_setupdone),
    .ep0_request                (ep0_request),
    .ep0_wvalue                 (ep0_wvalue),
    .ep0_windex                 (ep0_windex),
    .ep0_class_stall            (ep0_class_stall),

    .sync_suspend               (sync_suspend),
    .sync_busreset              (sync_busreset),
    .ep0_remote_wake_enabled_hub(ep0_remote_wake_enabled_hub),
    .hub_remotewakeup           (hub_remotewakeup)
  );

  // ---------------------------------------------------------------------------
  // Per-device observers (areas A-D)
  // ---------------------------------------------------------------------------
  // usb_reg_if_1 is DEV0 and usb_reg_if_2 is DEV1: the two instances are
  // distinguished by their C_DEV0_* / C_DEV1_* generic maps in the compound
  // structure. Everything read from them is genuinely per-device.
  //
  // The transaction layer, by contrast, is the single shared usb_pie_1 that is
  // time-multiplexed across hub + dev0 + dev1, so those nets are read once
  // here and the per-device attribution is done inside the observer using
  // pie_dev_selected. See usb_dev_ep_cov for why that is safe.
  localparam int unsigned DEV_SEL_DEV0 = usb_cov_pkg::USB_SEL_DEV0;
  localparam int unsigned DEV_SEL_DEV1 = usb_cov_pkg::USB_SEL_DEV1;

  // Shared PIE transaction layer.
  logic        pie_epinfo_req;
  logic        pie_epinfo_epnr_dir;
  logic [3:0]  pie_epinfo_epnr;
  logic        pie_endtransfer;
  logic        pie_success;
  logic        pie_error;
  logic [3:0]  pie_errortype;
  logic        pie_sent_nak;
  logic        epinfo_iso;
  logic        epinfo_stall;
  logic        epinfo_disabled;
  logic        epinfo_active;
  logic        epinfo_toggle;
  logic [14:0] epinfo_nbytes;
  logic        utmi_xcvrselect;
  logic        utmi_termselect;

  always_comb pie_epinfo_req      = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.pie_epinfo_req;
  always_comb pie_epinfo_epnr     = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.pie_epinfo_epnr;
  always_comb pie_epinfo_epnr_dir = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.pie_epinfo_epdir;
  always_comb pie_endtransfer     = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.pie_endtransfer;
  always_comb pie_success         = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.pie_success;
  always_comb pie_error           = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.pie_error;
  always_comb pie_errortype       = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.pie_errortype;
  always_comb pie_sent_nak        = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.pie_sentNAK;
  always_comb epinfo_iso          = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.epinfo_iso;
  always_comb epinfo_stall        = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.epinfo_stall;
  always_comb epinfo_disabled     = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.epinfo_disabled;
  always_comb epinfo_active       = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.epinfo_active;
  always_comb epinfo_toggle       = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.epinfo_toggle;
  always_comb epinfo_nbytes       = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.epinfo_nbytes;
  always_comb utmi_xcvrselect     = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.utmi_xcvrselect;
  always_comb utmi_termselect     = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_pie_1.utmi_termselect;

  // Per-device register state. The two generate-free register files are
  // directly named instances, so every field below is a plain port read.
  logic [6:0]  d0_usbaddress,  d1_usbaddress;
  logic        d0_deviceenabled, d1_deviceenabled;
  logic        d0_setup,       d1_setup;
  logic        d0_pll_on,      d1_pll_on;
  logic        d0_lpm_sup,     d1_lpm_sup;
  logic        d0_dev_connect, d1_dev_connect;
  logic        d0_sync_suspend, d1_sync_suspend;
  logic        d0_lpm_suspend, d1_lpm_suspend;
  logic        d0_lpm_rw,      d1_lpm_rw;
  logic        d0_force_fs,    d1_force_fs;
  logic [1:0]  d0_speed,       d1_speed;
  logic        d0_vbus_deb,    d1_vbus_deb;
  logic        d0_busreset,    d1_busreset;
  logic        d0_remotewakeup, d1_remotewakeup;
  logic        d0_lpmremotewakeup, d1_lpmremotewakeup;
  logic [3:0]  d0_hird_sw,     d1_hird_sw;
  logic [3:0]  d0_hird_hw,     d1_hird_hw;
  logic        d0_lpm_nyet,    d1_lpm_nyet;
  logic        d0_irq,         d1_irq;
  logic        d0_fiq,         d1_fiq;
  logic        d0_bufinuse_any, d1_bufinuse_any;
  logic        d0_skip_any,    d1_skip_any;

  // Interrupt register slices. usb_reg_if keeps INTSTAT, INTEN and INTROUTE as
  // three separate signals each (endpoint vector, frame bit, device bit); the
  // flat register word only exists on the readback path.
  logic [15:0] d0_ep_int_status,  d1_ep_int_status;
  logic        d0_frame_int_status, d1_frame_int_status;
  logic        d0_dev_int_status, d1_dev_int_status;
  logic [15:0] d0_ep_int_enable,  d1_ep_int_enable;
  logic        d0_frame_int_enable, d1_frame_int_enable;
  logic        d0_dev_int_enable, d1_dev_int_enable;
  logic [15:0] d0_ep_int_route,   d1_ep_int_route;
  logic        d0_frame_int_route, d1_frame_int_route;
  logic        d0_dev_int_route,  d1_dev_int_route;

  // CSR write decode, replicating the case on reg_waddr in proc_reg_write.
  logic        d0_reg_write,   d1_reg_write;
  logic [3:0]  d0_reg_waddr,   d1_reg_waddr;
  logic [31:0] d0_reg_wdata,   d1_reg_wdata;
  logic        d0_wr_intstat,  d1_wr_intstat;
  logic        d0_wr_inten,    d1_wr_inten;
  logic        d0_wr_intsetstat, d1_wr_intsetstat;
  logic        d0_wr_introute, d1_wr_introute;

  always_comb d0_usbaddress      = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.usbreg_usbaddress;
  always_comb d0_deviceenabled   = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.usbreg_deviceenabled;
  always_comb d0_setup           = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.usbreg_setup;
  always_comb d0_pll_on          = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.usbreg_pll_on;
  always_comb d0_lpm_sup         = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.usbreg_lpm_sup;
  always_comb d0_dev_connect     = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.usbreg_dev_connect;
  always_comb d0_sync_suspend    = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.sync_suspend;
  always_comb d0_lpm_suspend     = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.sync_lpm_Suspend;
  always_comb d0_lpm_rw          = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.sync_lpm_rw;
  always_comb d0_force_fs        = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.usbreg_port_force_fullspeed;
  always_comb d0_speed           = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.pie_speed;
  always_comb d0_vbus_deb        = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.sync_VBusDebounced;
  always_comb d0_busreset        = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.sync_busreset;
  always_comb d0_remotewakeup    = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.usbreg_remotewakeup;
  always_comb d0_lpmremotewakeup = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.usbreg_lpmremotewakeup;
  always_comb d0_hird_sw         = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.usbreg_lpm_hird_sw;
  always_comb d0_hird_hw         = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.sieint_lpm_hird_hw;
  always_comb d0_lpm_nyet        = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.usbreg_lpm_nyet;
  always_comb d0_irq             = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.USB_Int_Req_Irq;
  always_comb d0_fiq             = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.USB_Int_Req_Fiq;
  // EPSKIP and EPBUFINUSE are per-endpoint vectors; the observer only asks
  // whether any endpoint is using a second buffer or has been skipped.
  always_comb d0_bufinuse_any    = |caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.usbreg_ep_bufinuse;
  always_comb d0_skip_any        = |caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.usbreg_ep_skip;
  // PHY test mode is DEVCMDSTAT[31:29]. The hub itself has no usb_reg_if, but
  // the PHY is shared across the whole compound and all three functions drive
  // the one set of UTMI pins, so DEV0's copy is the subsystem-wide value and
  // is what usb_hub_cov's folded-in cp_phy_test_mode samples.
  always_comb d0_phy_test_mode   = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.usbreg_phy_test_mode;

  // Interrupt register state. These are architecture signals of usb_reg_if,
  // not ports: INTSTAT, INTEN and INTROUTE have no output pins, they only
  // appear on reg_rdata during a read. The observer needs the live value on
  // every cycle, so the internal signals are read directly. They are plain
  // std_logic / std_logic_vector, so the mixed-language XMR is well defined.
  always_comb d0_ep_int_status    = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.reg_ep_int_status;
  always_comb d0_frame_int_status = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.reg_frame_int_status;
  always_comb d0_dev_int_status   = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.reg_dev_int_status;
  always_comb d0_ep_int_enable    = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.reg_ep_int_enable;
  always_comb d0_frame_int_enable = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.reg_frame_int_enable;
  always_comb d0_dev_int_enable   = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.reg_dev_int_enable;
  always_comb d0_ep_int_route     = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.reg_ep_int_route;
  always_comb d0_frame_int_route  = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.reg_frame_int_route;
  always_comb d0_dev_int_route    = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.reg_dev_int_route;

  // CSR write port. proc_reg_write qualifies its case on reg_write, so the
  // same qualification is applied here to produce one strobe per interrupt
  // register. The word numbers are the "1000" .. "1011" branch labels.
  always_comb d0_reg_write = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.reg_write;
  always_comb d0_reg_waddr = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.reg_waddr;
  always_comb d0_reg_wdata = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_1.reg_wdata;

  always_comb d0_wr_intstat    = d0_reg_write && (d0_reg_waddr == usb_cov_pkg::DEV_CSR_INTSTAT);
  always_comb d0_wr_inten      = d0_reg_write && (d0_reg_waddr == usb_cov_pkg::DEV_CSR_INTEN);
  always_comb d0_wr_intsetstat = d0_reg_write && (d0_reg_waddr == usb_cov_pkg::DEV_CSR_INTSETSTAT);
  always_comb d0_wr_introute   = d0_reg_write && (d0_reg_waddr == usb_cov_pkg::DEV_CSR_INTROUTE);

  always_comb d1_usbaddress      = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.usbreg_usbaddress;
  always_comb d1_deviceenabled   = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.usbreg_deviceenabled;
  always_comb d1_setup           = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.usbreg_setup;
  always_comb d1_pll_on          = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.usbreg_pll_on;
  always_comb d1_lpm_sup         = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.usbreg_lpm_sup;
  always_comb d1_dev_connect     = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.usbreg_dev_connect;
  always_comb d1_sync_suspend    = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.sync_suspend;
  always_comb d1_lpm_suspend     = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.sync_lpm_Suspend;
  always_comb d1_lpm_rw          = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.sync_lpm_rw;
  always_comb d1_force_fs        = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.usbreg_port_force_fullspeed;
  always_comb d1_speed           = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.pie_speed;
  always_comb d1_vbus_deb        = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.sync_VBusDebounced;
  always_comb d1_busreset        = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.sync_busreset;
  always_comb d1_remotewakeup    = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.usbreg_remotewakeup;
  always_comb d1_lpmremotewakeup = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.usbreg_lpmremotewakeup;
  always_comb d1_hird_sw         = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.usbreg_lpm_hird_sw;
  always_comb d1_hird_hw         = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.sieint_lpm_hird_hw;
  always_comb d1_lpm_nyet        = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.usbreg_lpm_nyet;
  always_comb d1_irq             = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.USB_Int_Req_Irq;
  always_comb d1_fiq             = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.USB_Int_Req_Fiq;
  always_comb d1_bufinuse_any    = |caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.usbreg_ep_bufinuse;
  always_comb d1_skip_any        = |caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.usbreg_ep_skip;
  always_comb d1_phy_test_mode   = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.usbreg_phy_test_mode;

  always_comb d1_ep_int_status    = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.reg_ep_int_status;
  always_comb d1_frame_int_status = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.reg_frame_int_status;
  always_comb d1_dev_int_status   = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.reg_dev_int_status;
  always_comb d1_ep_int_enable    = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.reg_ep_int_enable;
  always_comb d1_frame_int_enable = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.reg_frame_int_enable;
  always_comb d1_dev_int_enable   = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.reg_dev_int_enable;
  always_comb d1_ep_int_route     = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.reg_ep_int_route;
  always_comb d1_frame_int_route  = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.reg_frame_int_route;
  always_comb d1_dev_int_route    = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.reg_dev_int_route;

  always_comb d1_reg_write = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.reg_write;
  always_comb d1_reg_waddr = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.reg_waddr;
  always_comb d1_reg_wdata = caliptra_ss_top_tb.caliptra_ss_dut.usb_core_i.u_hub_compound.usb_reg_if_2.reg_wdata;

  always_comb d1_wr_intstat    = d1_reg_write && (d1_reg_waddr == usb_cov_pkg::DEV_CSR_INTSTAT);
  always_comb d1_wr_inten      = d1_reg_write && (d1_reg_waddr == usb_cov_pkg::DEV_CSR_INTEN);
  always_comb d1_wr_intsetstat = d1_reg_write && (d1_reg_waddr == usb_cov_pkg::DEV_CSR_INTSETSTAT);
  always_comb d1_wr_introute   = d1_reg_write && (d1_reg_waddr == usb_cov_pkg::DEV_CSR_INTROUTE);

  // Area A: link power state, per device.
  usb_dev_link_cov #(.DEV_NAME("dev0")) u_dev0_link_cov (
    .clk              (clk),
    .rst_n            (rst_n),
    .dcon             (d0_dev_connect),
    .dsus             (d0_sync_suspend),
    .lpm_sus          (d0_lpm_suspend),
    .lpm_rewp         (d0_lpm_rw),
    .speed            (d0_speed),
    .remotewakeup     (d0_remotewakeup),
    .lpm_remotewakeup (d0_lpmremotewakeup),
    .busreset         (d0_busreset),
    .lpm_hird_sw      (d0_hird_sw),
    .lpm_hird_hw      (d0_hird_hw),
    .lpm_nyet         (d0_lpm_nyet),
    .force_needclk    (d0_pll_on),
    .vbus_debounced   (d0_vbus_deb)
  );

  usb_dev_link_cov #(.DEV_NAME("dev1")) u_dev1_link_cov (
    .clk              (clk),
    .rst_n            (rst_n),
    .dcon             (d1_dev_connect),
    .dsus             (d1_sync_suspend),
    .lpm_sus          (d1_lpm_suspend),
    .lpm_rewp         (d1_lpm_rw),
    .speed            (d1_speed),
    .remotewakeup     (d1_remotewakeup),
    .lpm_remotewakeup (d1_lpmremotewakeup),
    .busreset         (d1_busreset),
    .lpm_hird_sw      (d1_hird_sw),
    .lpm_hird_hw      (d1_hird_hw),
    .lpm_nyet         (d1_lpm_nyet),
    .force_needclk    (d1_pll_on),
    .vbus_debounced   (d1_vbus_deb)
  );

  // Area B: enumeration and connection, per device.
  usb_dev_enum_cov #(.DEV_NAME("dev0")) u_dev0_enum_cov (
    .clk             (clk),
    .rst_n           (rst_n),
    .dev_addr        (d0_usbaddress),
    .dev_en          (d0_deviceenabled),
    .setup           (d0_setup),
    .dcon            (d0_dev_connect),
    .dsus            (d0_sync_suspend),
    .lpm_sus         (d0_lpm_suspend),
    .force_fs        (d0_force_fs),
    .speed           (d0_speed),
    .vbus_debounced  (d0_vbus_deb),
    .busreset        (d0_busreset),
    .utmi_xcvrselect (utmi_xcvrselect),
    .utmi_termselect (utmi_termselect)
  );

  usb_dev_enum_cov #(.DEV_NAME("dev1")) u_dev1_enum_cov (
    .clk             (clk),
    .rst_n           (rst_n),
    .dev_addr        (d1_usbaddress),
    .dev_en          (d1_deviceenabled),
    .setup           (d1_setup),
    .dcon            (d1_dev_connect),
    .dsus            (d1_sync_suspend),
    .lpm_sus         (d1_lpm_suspend),
    .force_fs        (d1_force_fs),
    .speed           (d1_speed),
    .vbus_debounced  (d1_vbus_deb),
    .busreset        (d1_busreset),
    .utmi_xcvrselect (utmi_xcvrselect),
    .utmi_termselect (utmi_termselect)
  );

  // Areas C and D: endpoints, transfers and interrupts, per device. The PIE
  // nets are shared, so MY_SEL selects which traffic each instance counts.
  usb_dev_ep_cov #(
    .DEV_NAME ("dev0"),
    .MY_SEL   (DEV_SEL_DEV0)
  ) u_dev0_ep_cov (
    .clk              (clk),
    .rst_n            (rst_n),
    .pie_dev_selected (pie_dev_selected),
    .epinfo_req       (pie_epinfo_req),
    .endtransfer      (pie_endtransfer),
    .ep_num           (pie_epinfo_epnr),
    .ep_dir           (pie_epinfo_epnr_dir),
    .ep_iso           (epinfo_iso),
    .ep_stall         (epinfo_stall),
    .ep_disabled      (epinfo_disabled),
    .ep_active        (epinfo_active),
    .ep_toggle        (epinfo_toggle),
    .ep_nbytes        (epinfo_nbytes),
    .xfer_success     (pie_success),
    .xfer_error       (pie_error),
    .xfer_errortype   (pie_errortype),
    .xfer_sent_nak    (pie_sent_nak),
    .ep_bufinuse_any  (d0_bufinuse_any),
    .ep_skip_any      (d0_skip_any),
    .usb_irq          (d0_irq),
    .usb_fiq          (d0_fiq),
    .dcon             (d0_dev_connect),
    .dsus             (d0_sync_suspend),
    .lpm_sus          (d0_lpm_suspend)
  );

  usb_dev_ep_cov #(
    .DEV_NAME ("dev1"),
    .MY_SEL   (DEV_SEL_DEV1)
  ) u_dev1_ep_cov (
    .clk              (clk),
    .rst_n            (rst_n),
    .pie_dev_selected (pie_dev_selected),
    .epinfo_req       (pie_epinfo_req),
    .endtransfer      (pie_endtransfer),
    .ep_num           (pie_epinfo_epnr),
    .ep_dir           (pie_epinfo_epnr_dir),
    .ep_iso           (epinfo_iso),
    .ep_stall         (epinfo_stall),
    .ep_disabled      (epinfo_disabled),
    .ep_active        (epinfo_active),
    .ep_toggle        (epinfo_toggle),
    .ep_nbytes        (epinfo_nbytes),
    .xfer_success     (pie_success),
    .xfer_error       (pie_error),
    .xfer_errortype   (pie_errortype),
    .xfer_sent_nak    (pie_sent_nak),
    .ep_bufinuse_any  (d1_bufinuse_any),
    .ep_skip_any      (d1_skip_any),
    .usb_irq          (d1_irq),
    .usb_fiq          (d1_fiq),
    .dcon             (d1_dev_connect),
    .dsus             (d1_sync_suspend),
    .lpm_sus          (d1_lpm_suspend)
  );

  // Area D2: interrupt registers, per device and per source. Everything here
  // is genuinely per-device register state, so no PIE qualification applies.
  // NUM_PHYS_EP is C_NBPHYSEP+2 = 16, the width of the reg_ep_int_* slices.
  usb_dev_irq_cov #(
    .DEV_NAME    ("dev0"),
    .NUM_PHYS_EP (16)
  ) u_dev0_irq_cov (
    .clk              (clk),
    .rst_n            (rst_n),
    .ep_int_status    (d0_ep_int_status),
    .frame_int_status (d0_frame_int_status),
    .dev_int_status   (d0_dev_int_status),
    .ep_int_enable    (d0_ep_int_enable),
    .frame_int_enable (d0_frame_int_enable),
    .dev_int_enable   (d0_dev_int_enable),
    .ep_int_route     (d0_ep_int_route),
    .frame_int_route  (d0_frame_int_route),
    .dev_int_route    (d0_dev_int_route),
    .wr_intstat       (d0_wr_intstat),
    .wr_inten         (d0_wr_inten),
    .wr_intsetstat    (d0_wr_intsetstat),
    .wr_introute      (d0_wr_introute),
    .wr_data          (d0_reg_wdata),
    .usb_irq          (d0_irq),
    .usb_fiq          (d0_fiq),
    .dcon             (d0_dev_connect),
    .dsus             (d0_sync_suspend),
    .lpm_sus          (d0_lpm_suspend)
  );

  usb_dev_irq_cov #(
    .DEV_NAME    ("dev1"),
    .NUM_PHYS_EP (16)
  ) u_dev1_irq_cov (
    .clk              (clk),
    .rst_n            (rst_n),
    .ep_int_status    (d1_ep_int_status),
    .frame_int_status (d1_frame_int_status),
    .dev_int_status   (d1_dev_int_status),
    .ep_int_enable    (d1_ep_int_enable),
    .frame_int_enable (d1_frame_int_enable),
    .dev_int_enable   (d1_dev_int_enable),
    .ep_int_route     (d1_ep_int_route),
    .frame_int_route  (d1_frame_int_route),
    .dev_int_route    (d1_dev_int_route),
    .wr_intstat       (d1_wr_intstat),
    .wr_inten         (d1_wr_inten),
    .wr_intsetstat    (d1_wr_intsetstat),
    .wr_introute      (d1_wr_introute),
    .wr_data          (d1_reg_wdata),
    .usb_irq          (d1_irq),
    .usb_fiq          (d1_fiq),
    .dcon             (d1_dev_connect),
    .dsus             (d1_sync_suspend),
    .lpm_sus          (d1_lpm_suspend)
  );

  // ---------------------------------------------------------------------------
  // Area F: compound multiplexing and cross-function concurrency
  // ---------------------------------------------------------------------------
  // Single instance: every question it asks is about the relationship BETWEEN
  // the functions, so there is nothing per-device to instance.
  usb_compound_cov #(
    .NUM_HW_DEVICES (NUM_HW_DEVICES)
  ) u_usb_compound_cov (
    .clk                (clk),
    .rst_n              (rst_n),

    .pie_dev_selected   (pie_dev_selected),
    .dma_ahb_selected   (dma_ahb_selected),

    .deviceenabled_hub  (deviceenabled_hub),
    .deviceenabled_dev0 (deviceenabled_dev0),
    .deviceenabled_dev1 (deviceenabled_dev1),

    .hub_enable         (hub_enable),

    .dev0_dcon          (d0_dev_connect),
    .dev0_dsus          (d0_sync_suspend),
    .dev0_lpm_sus       (d0_lpm_suspend),
    .dev0_addr          (d0_usbaddress),
    .dev1_dcon          (d1_dev_connect),
    .dev1_dsus          (d1_sync_suspend),
    .dev1_lpm_sus       (d1_lpm_suspend),
    .dev1_addr          (d1_usbaddress)
  );

`endif // USB_FCOV

endmodule

// File contains AI-generated response based on internal company sources
