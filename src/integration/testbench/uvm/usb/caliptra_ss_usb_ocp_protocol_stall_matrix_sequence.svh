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

`ifndef CALIPTRA_SS_USB_OCP_PROTOCOL_STALL_MATRIX_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_PROTOCOL_STALL_MATRIX_SEQUENCE_SV

// Directed sequence for persistent protocol STALL and coded errors:
//   OCP Recovery v1.1 Section 8.5.1 (encapsulation and wLength rules)
//   OCP Recovery v1.1 Section 9.1  (protocol error handling)
//   USB 2.0 Section 8.5.3.4        (protocol STALL persistence)
//
// The sequence exercises, in a single arbiter-observed run:
//   1. Normal unclaimed enumeration and one clean claimed PROT_CAP window.
//      The claimed window is observed by the arbiter_checker configured
//      for mirrored_setup_mode=1, which now compares the mirrored SETUP
//      SRAM contents against the host-transmitted 8 SETUP bytes and
//      requires at least one SETUP-aperture SRAM write.
//   2. Persistent STALL cross-token PROXY: after an unsupported command
//      error, repeated identical erroneous EP0 CONTROL transfers must
//      continue to report non-SUCCESS on every iteration (each aggregate
//      result is not ACK/PASS). The Synopsys svt_usb_transfer host API
//      cannot inject bare IN/OUT/PING tokens between SETUPs, so this is
//      a proxy for USB 2.0 Sec 8.5.3.4 token-level persistence, not the
//      full check.
//   3. Error-code matrix: 0x01 unsupported/host-RO, 0x03 wrong write count,
//      0xFF wrong read length. Each error is paired with STALL and cleared
//      by a Recovery Agent DEVICE_STATUS read.
//   4. First-error-wins: error A (0x01 UNSUPPORTED) then a distinct error
//      B (0x03 LENGTH) must not overwrite the sticky code; the RA read
//      still returns 0x01.
//   5. Repeated invalid SETUP holds persistent stall: per-iteration STALL
//      is enforced and the sticky code must not drift across the loop.
//      A legal DEVICE_STATUS SETUP is then the release path.
//   6. Standard requests (non-OCP-claimed SETUP) never set PROTOCOL_ERROR,
//      with an explicit PROT_ERROR==0 precondition before the standard
//      request so a stale sticky value cannot masquerade as a pollution
//      failure.
//   7. Final PROT_CAP after the matrix confirms the release path is intact.
//   8. Passive: non-EP0 probe skipped with an explicit warning when the VIP
//      topology does not carry a non-EP0 endpoint.
//
// Stimulus limitations for the DV handoff:
//   * The Synopsys svt_usb_transfer host-side API drives complete CONTROL
//     transfers; bare IN/OUT/PING tokens between SETUPs are not available.
//     Persistent STALL across non-SETUP tokens is only exercised as a
//     CONTROL-transfer repeat, not a true single-SETUP token-level probe.
//   * CRC/PHY-failure SETUP corruption is not offered by the current base
//     sequences. The intent "CRC/PHY failure sets no OCP error" is
//     approximated here only by proving that a STANDARD (non-OCP-claimed)
//     SETUP does not touch PROT_ERROR; a full CRC-injection check must
//     come from a follow-on bare-PHY integration test.

class caliptra_ss_usb_ocp_protocol_stall_matrix_sequence
    extends caliptra_ss_usb_ocp_post_sync_arbiter_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_protocol_stall_matrix_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    protected int unsigned matrix_checks_passed;

    function new(string name = "caliptra_ss_usb_ocp_protocol_stall_matrix_sequence");
        super.new(name);
        matrix_checks_passed = 0;
    endfunction

    protected virtual task mark_matrix(input string label);
        matrix_checks_passed++;
        `uvm_info("OCP_PROTOCOL_STALL",
            $sformatf("[PROTOCOL_STALL] check=%0d %s", matrix_checks_passed, label),
            UVM_NONE)
    endtask

    // Issue an erroneous OCP transfer and require a STALL packet. The VIP
    // classifies a control transfer terminated by STALL as ABORTED, so the
    // packet callback supplies the protocol-level evidence.
    protected virtual task issue_expected_stall(
        input bit dir_in,
        input ocp_cmd_t cmd_code,
        input bit [15:0] wlength,
        ref bit [7:0] payload_bytes[$],
        input string label);

        caliptra_ss_usb_ocp_xfer_result_e result;
        bit [7:0] resp_bytes[$];
        int unsigned stall_count;

        checker.packet_callback.start_window(snapshot_generation);
        snapshot_generation++;
        ocp_class_xfer_result(
            dir_in, cmd_code, wlength,
            payload_bytes, resp_bytes, result, label);
        checker.packet_callback.stop_window();
        stall_count = checker.packet_callback.count_pid(
            svt_usb_packet::STALL,
            caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_RX);
        if (stall_count == 0) begin
            `uvm_error("OCP_PROTOCOL_STALL",
                $sformatf("%s: no device STALL packet was observed.", label))
        end
        if (result == OCP_XFER_SUCCESS) begin
            `uvm_error("OCP_PROTOCOL_STALL",
                $sformatf({"%s: erroneous transfer reported SUCCESS; ",
                           "spec requires STALL and PROTOCOL_ERROR."}, label))
        end
    endtask

    // Repeated non-successful CONTROL transfer with the same illegal
    // parameters. If the device correctly holds C_PROT_STALL through the
    // repeat's data/status stage (and cleanly re-enters stall on the next
    // SETUP because the SETUP itself is again illegal), the aggregate result
    // remains non-success on every repeat.
    protected virtual task probe_stall_persistence(
        input bit dir_in,
        input ocp_cmd_t cmd_code,
        input bit [15:0] wlength,
        ref bit [7:0] payload_bytes[$],
        input int unsigned repeats,
        input string label);

        for (int unsigned i = 0; i < repeats; i++) begin
            issue_expected_stall(
                dir_in, cmd_code, wlength, payload_bytes,
                $sformatf("%s_probe_%0d", label, i));
        end
    endtask

    // Perform one erroneous transfer then verify: (a) the DEVICE_STATUS
    // PROT_ERROR reports the expected code and (b) a second RA read clears
    // it to 0. The read step also drives the valid-new-SETUP release path
    // so subsequent legal traffic is checked to succeed.
    // Read PROT_ERROR by driving a RA DEVICE_STATUS read (destructive: the
    // sticky code clears on the completed RA read). Returns the observed
    // code or invokes a hard error when the read is truncated.
    protected virtual task ra_read_prot_error(
        input string label,
        output bit [7:0] code);

        bit [7:0] device_status[$];
        code = 8'h00;
        device_status_read_and_check(device_status, label);
        if (device_status.size() <= OCP_OFF_DS_PROT_ERROR) begin
            `uvm_error("OCP_PROTOCOL_STALL",
                $sformatf({"%s: DEVICE_STATUS truncated to %0d bytes; ",
                           "PROT_ERROR unobservable."},
                          label, device_status.size()))
            return;
        end
        code = device_status[OCP_OFF_DS_PROT_ERROR];
    endtask

    protected virtual task expect_error_and_release(
        input bit dir_in,
        input ocp_cmd_t cmd_code,
        input bit [15:0] wlength,
        ref bit [7:0] payload_bytes[$],
        input ocp_protocol_error_e expected_code,
        input string label);

        bit [7:0] code_after_err;
        bit [7:0] code_after_clear;

        issue_expected_stall(
            dir_in, cmd_code, wlength, payload_bytes,
            $sformatf("%s_ERR", label));

        ra_read_prot_error(
            $sformatf("%s_READ_CODE", label), code_after_err);
        if (code_after_err != expected_code) begin
            `uvm_error("OCP_PROTOCOL_STALL",
                $sformatf({"%s: PROT_ERROR=0x%02h expected 0x%02h ",
                           "(OCP Recovery v1.1 Sec 9.1)."},
                          label, code_after_err, expected_code))
        end

        ra_read_prot_error(
            $sformatf("%s_READ_CLEAR", label), code_after_clear);
        if (code_after_clear != OCP_PROTOCOL_ERROR_NONE) begin
            `uvm_error("OCP_PROTOCOL_STALL",
                $sformatf({"%s: PROT_ERROR did not clear on the RA read: ",
                           "got 0x%02h."},
                          label, code_after_clear))
        end
        mark_matrix($sformatf("%s coded 0x%02h and cleared on RA read",
                              label, expected_code));
    endtask

    // First-error-wins: error A must produce code 0x01 (UNSUPPORTED). Error
    // B must be a DIFFERENT triggerable code (0x03 LENGTH via a
    // fixed-length write with wrong count on RECOVERY_CTRL). If the DUT
    // correctly latches first-error-wins, the RA read still sees 0x01.
    protected virtual task check_first_error_wins();
        bit [7:0] one_byte[$];
        bit [7:0] code_after_ab;
        bit [7:0] code_after_clear;

        one_byte = '{ 8'hAA };

        // Error A: unsupported/reserved command code. Byte 0x21 is outside
        // OCP_CMD_MIN..OCP_CMD_MAX so it is definitively unsupported per
        // OCP Recovery v1.1 Sec 8.5.
        issue_expected_stall(
            1'b0, 8'h21, 16'd1, one_byte, "STALL_FEW_ERR_A_UNSUPPORTED");

        // Error B: fixed-length command with wrong write count -> LENGTH
        // (0x03). RECOVERY_CTRL has a required byte count of 3; issuing
        // wLength=1 is a length-error path. If the DUT overwrote the sticky
        // field, the follow-up RA read would report 0x03 rather than 0x01.
        issue_expected_stall(
            1'b0, OCP_CMD_RECOVERY_CTRL, 16'd1, one_byte,
            "STALL_FEW_ERR_B_LENGTH");

        ra_read_prot_error("STALL_FEW_READ_FIRST", code_after_ab);
        if (code_after_ab != OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND) begin
            `uvm_error("OCP_PROTOCOL_STALL",
                $sformatf({"First-error-wins: expected 0x01 (UNSUPPORTED) ",
                           "after A(0x01)+B(0x03); got 0x%02h."},
                          code_after_ab))
        end

        ra_read_prot_error("STALL_FEW_READ_CLEAR", code_after_clear);
        if (code_after_clear != OCP_PROTOCOL_ERROR_NONE) begin
            `uvm_error("OCP_PROTOCOL_STALL",
                $sformatf({"First-error-wins: PROT_ERROR did not clear on ",
                           "the second RA read: got 0x%02h."},
                          code_after_clear))
        end
        mark_matrix(
            "first-error-wins retained 0x01 across a distinct 0x03 error");
    endtask

    // Repeated invalid SETUP holds persistent stall: per-iteration
    // outcome must remain non-SUCCESS (stalled), the sticky code must not
    // drift across the repeats, and finally a legal DEVICE_STATUS SETUP
    // clears the code on RA read as the documented release path.
    //
    // API note: neither the base sequence nor svt_usb_transfer expose a
    // non-clearing PROT_ERROR read from the USB side, so first_code is
    // sourced from an RA read after a leading erroneous SETUP; the loop's
    // integrity is checked by (i) per-iteration STALL result, and (ii) the
    // post-loop RA read returning the same code (which reappears because
    // every repeat produces the identical LENGTH error).
    protected virtual task check_repeated_invalid_setup_holds_stall();
        bit [7:0] payload_one[$];
        caliptra_ss_usb_ocp_xfer_result_e iter_result;
        bit [7:0] iter_resp[$];
        bit [7:0] first_code;
        bit [7:0] after_loop_code;
        bit [7:0] release_code;
        int unsigned stall_count;

        payload_one = '{ 8'h5A };

        // Prime: one erroneous SETUP so PROT_ERROR is set (LENGTH 0x03 on
        // RECOVERY_CTRL which requires a 3-byte write).
        issue_expected_stall(
            1'b0, OCP_CMD_RECOVERY_CTRL, 16'd1, payload_one,
            "STALL_REPEAT_INVALID_PRIME");
        ra_read_prot_error("STALL_REPEAT_INVALID_PRIME_CODE", first_code);
        if (first_code != OCP_PROTOCOL_ERROR_LENGTH) begin
            `uvm_error("OCP_PROTOCOL_STALL",
                $sformatf({"Repeated-invalid prime: expected LENGTH 0x03 ",
                           "on RECOVERY_CTRL wLength=1; got 0x%02h."},
                          first_code))
        end

        // Loop: every iteration is the same error and must produce STALL
        // per USB 2.0 Sec 8.5.3.4.
        for (int unsigned i = 0; i < 4; i++) begin
            checker.packet_callback.start_window(snapshot_generation);
            snapshot_generation++;
            ocp_class_xfer_result(
                1'b0, OCP_CMD_RECOVERY_CTRL, 16'd1, payload_one,
                iter_resp, iter_result,
                $sformatf("STALL_REPEAT_INVALID_%0d", i));
            checker.packet_callback.stop_window();
            stall_count = checker.packet_callback.count_pid(
                svt_usb_packet::STALL,
                caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_RX);
            if (stall_count == 0) begin
                `uvm_error("OCP_PROTOCOL_STALL",
                    $sformatf("Repeat %0d produced no device STALL packet.", i))
            end
            if (iter_result == OCP_XFER_SUCCESS) begin
                `uvm_error("OCP_PROTOCOL_STALL",
                    $sformatf({"Repeat %0d unexpectedly SUCCEEDED; persistent ",
                               "stall must hold across repeated invalid SETUP."},
                              i))
            end else begin
                `uvm_info("OCP_PROTOCOL_STALL",
                    $sformatf({"[PROTOCOL_STALL] repeat %0d observed %0d STALL ",
                               "packet(s), result=%s."},
                              i, stall_count, iter_result.name()), UVM_NONE)
            end
        end

        // After the loop, the sticky code must not have drifted: each
        // repeat produced the same LENGTH error, so the current sticky is
        // still 0x03 (either retained across the loop, or re-set on the
        // last iteration).
        ra_read_prot_error("STALL_REPEAT_INVALID_READ", after_loop_code);
        if (after_loop_code != first_code) begin
            `uvm_error("OCP_PROTOCOL_STALL",
                $sformatf({"Repeated invalid loop mutated PROT_ERROR from ",
                           "0x%02h to 0x%02h; corrupt/unsuccessful replacement ",
                           "must not overwrite the sticky code (plan Sec 8.5, ",
                           "USB 2.0 Sec 8.5.3.4)."},
                          first_code, after_loop_code))
        end

        // Release path: a legal DEVICE_STATUS SETUP is a "valid new SETUP",
        // which per USB 2.0 Sec 8.5.3.4 releases the persistent stall. The
        // completed RA read then clears the sticky code.
        ra_read_prot_error("STALL_REPEAT_INVALID_RELEASE", release_code);
        if (release_code != OCP_PROTOCOL_ERROR_NONE) begin
            `uvm_error("OCP_PROTOCOL_STALL",
                $sformatf({"Release path: PROT_ERROR did not clear on ",
                           "legal DEVICE_STATUS RA read: got 0x%02h."},
                          release_code))
        end
        mark_matrix(
            "persistent stall held across four repeated invalid SETUPs then released");
    endtask

    // Prove a standard (non-OCP-claimed) SETUP does not touch PROT_ERROR.
    // Runnable proxy for "CRC/PHY failure produces no OCP error/stall":
    // the OCP claim gate must ignore transfers it does not recognize as
    // its own, including corrupt SETUPs which are also not recognized as
    // claimed. Precondition: ensure PROT_ERROR baseline is 0 before the
    // standard request so a stale sticky value from a prior sub-test does
    // not masquerade as a pollution failure or a false pass.
    protected virtual task check_standard_request_bypasses_ocp();
        bit [7:0] descriptor[$];
        bit [7:0] pre_code;
        bit [7:0] post_code;

        ra_read_prot_error("STALL_STD_CFG_BASELINE", pre_code);
        if (pre_code != OCP_PROTOCOL_ERROR_NONE) begin
            `uvm_error("OCP_PROTOCOL_STALL",
                $sformatf({"Standard bypass baseline: PROT_ERROR was 0x%02h ",
                           "before the standard request; expected 0x00. ",
                           "Preceding sub-test did not clear its state."},
                          pre_code))
        end

        standard_get_configuration_descriptor(9, descriptor, "STALL_STD_CFG");
        ra_read_prot_error("STALL_STD_CFG_STATUS", post_code);
        if (post_code != OCP_PROTOCOL_ERROR_NONE) begin
            `uvm_error("OCP_PROTOCOL_STALL",
                $sformatf({"Standard request (bRequest=0x06) polluted OCP ",
                           "PROT_ERROR with 0x%02h; standard requests must ",
                           "not enter OCP protocol stall."},
                          post_code))
        end
        mark_matrix("standard request left OCP PROT_ERROR untouched");
    endtask

    // Arbiter observation: one unclaimed enumeration + one clean claimed
    // PROT_CAP window under the mirrored-SETUP expectations. The
    // arbiter_checker itself (mirrored_setup_mode=1) enforces permitted vs
    // suppressed effects.
    protected virtual task arbiter_window_normal_claim();
        bit [7:0] response[$];
        logic [15:0] gen;

        open_observation_window(gen);
        ocp_read(OCP_CMD_PROT_CAP, response, "STALL_PROT_CAP_CLAIMED");
        // Claimed PROT_CAP under mirrored SETUP must not advance the legacy
        // SETUP-dispatch counter: DISPATCH_COUNT is a suppressed effect in
        // the mirrored-SETUP arbiter checker contract. Pass a
        // zero-delta expectation to close_observation_window so the
        // firmware/checker handshake sees no dispatch delta for this window.
        close_observation_window(gen, 4'h0);
        mark_matrix("claimed PROT_CAP window checked under mirrored SETUP");
    endtask

    // Non-EP0 traffic during EP0 stall/claim: unless the current VIP
    // topology exposes a claimed non-EP0 endpoint, this is an environment
    // limitation to log. Report explicitly here so nightly triage does not
    // treat absence-of-check as pass.
    protected virtual function bit env_has_non_ep0_endpoint();
        if ((usb_cfg == null) ||
            (usb_cfg.remote_device_cfg.size() == 0)) begin
            return 1'b0;
        end
        return (usb_cfg.remote_device_cfg[0].endpoint_cfg.size() > 1);
    endfunction

    protected virtual task report_non_ep0_environment();
        if (env_has_non_ep0_endpoint()) begin
            `uvm_info("OCP_PROTOCOL_STALL",
                $sformatf({"Non-EP0 endpoint present in VIP topology ",
                           "(endpoint_cfg count=%0d); non-EP0 traffic during ",
                           "OCP claim/stall is exercised by ARB005/ARB007 ",
                           "and left to those runs to avoid duplicate coverage."},
                          usb_cfg.remote_device_cfg[0].endpoint_cfg.size()),
                UVM_NONE)
            mark_matrix("non-EP0 topology reported for reservation checks");
        end else begin
            `uvm_warning("OCP_PROTOCOL_STALL",
                {"INTEGRATION_INCOMPLETE: current VIP topology exposes only ",
                 "EP0; non-EP0 traffic during OCP claim/stall cannot be ",
                 "exercised from this test. Coverage deferred to compound/hub ",
                 "topology or block-level assertion."})
        end
    endtask

    virtual task body();
        bit [7:0] payload_one[$];
        bit [7:0] payload_zero[$];
        bit [7:0] response[$];

        initialize_arbiter_transport();
        report_non_ep0_environment();

        // (1) Unclaimed enumeration already ran through initialize; open one
        //     claimed window to prove mirrored-SETUP expectations hold on a
        //     legal claimed transfer.
        arbiter_window_normal_claim();

        // (2) Persistent STALL cross-token proxy: unsupported command
        //     repeated four times must not slip through to SUCCESS.
        payload_one = '{ 8'h55 };
        probe_stall_persistence(
            1'b0, 8'h20, 16'd1, payload_one, 4, "STALL_PERSIST_UNSUPPORTED");
        mark_matrix("persistent STALL held across four unsupported repeats");

        // (3) Error-code matrix. Each entry also validates DEVICE_STATUS
        //     read/clear semantics.
        payload_one = '{ 8'hA5 };
        expect_error_and_release(
            1'b0, 8'h21, 16'd1, payload_one,
            OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND,
            "STALL_MATRIX_0x01_UNSUPPORTED_CODE");

        payload_one = '{ 8'hA5 };
        expect_error_and_release(
            1'b0, OCP_CMD_PROT_CAP, 16'd1, payload_one,
            OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND,
            "STALL_MATRIX_0x01_HOST_RO_WRITE");

        // Wrong write count on RECOVERY_CTRL: the fixed length is 3 bytes;
        // a 1-byte write must be rejected with 0x03.
        payload_one = '{ 8'h11 };
        expect_error_and_release(
            1'b0, OCP_CMD_RECOVERY_CTRL, 16'd1, payload_one,
            OCP_PROTOCOL_ERROR_LENGTH,
            "STALL_MATRIX_0x03_WRONG_WRITE_COUNT");

        // Wrong read length on DEVICE_STATUS: request 1 byte instead of the
        // advertised wMaxRdTransferSize and must produce 0xFF.
        payload_zero.delete();
        expect_error_and_release(
            1'b1, OCP_CMD_DEVICE_STATUS, 16'd1, payload_zero,
            OCP_PROTOCOL_ERROR_GENERAL,
            "STALL_MATRIX_0xFF_WRONG_READ_LENGTH");

        // (4) Sticky-code precedence.
        check_first_error_wins();

        // (5) Corrupt/unsuccessful replacement proxy.
        check_repeated_invalid_setup_holds_stall();

        // (6) Standard request bypasses OCP claim.
        check_standard_request_bypasses_ocp();

        // (7) Valid new SETUP releases stall: prove PROT_CAP still succeeds
        //     after the matrix.
        ocp_read(OCP_CMD_PROT_CAP, response, "STALL_FINAL_PROT_CAP");
        if (response.size() != OCP_SPEC_LEN_PROT_CAP) begin
            `uvm_error("OCP_PROTOCOL_STALL",
                $sformatf({"Post-matrix PROT_CAP length=%0d, expected %0d; ",
                           "persistent stall may not have released."},
                          response.size(), OCP_SPEC_LEN_PROT_CAP))
        end else begin
            mark_matrix("PROT_CAP after matrix succeeded (stall released)");
        end

        publish_transfer_count();
        wait_mcu_axi_idle_before_finish("PROTOCOL_STALL_MATRIX_FINISH");

        `uvm_info("OCP_PROTOCOL_STALL",
            $sformatf({"[PROTOCOL_STALL] stall and error matrix complete: ",
                       "checks_passed=%0d transfers_issued=%0d."},
                      matrix_checks_passed, transfers_issued),
            UVM_NONE)
    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_PROTOCOL_STALL_MATRIX_SEQUENCE_SV
