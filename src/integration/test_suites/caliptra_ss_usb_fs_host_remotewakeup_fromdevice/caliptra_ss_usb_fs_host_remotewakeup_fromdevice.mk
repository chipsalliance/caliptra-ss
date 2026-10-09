# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# Per-test makefile fragment, pulled in by tools/scripts/Makefile through
# "-include $(TEST_DIR)/$(TESTNAME).mk". It is read only when
# TESTNAME=caliptra_ss_usb_fs_host_remotewakeup_fromdevice, so it cannot
# affect any other test.
#
# Enables caliptra_ss_usb_suspend_resume_checker, which owns CHK_SUSPEND_SEEN
# and CHK_RESUME_SEEN on the DUT UTMI SuspendM output. Global L2 suspend does
# actuate on this IP (unlike hub downstream PORT_SUSPEND), so both edges are
# expected here and the checker is a real verdict rather than a formality.
#
# The "=1" form is kept for consistency with the test yml; $test$plusargs
# matches on prefix, so the value itself is ignored.
VCS_SIM_OPTS += +usb_suspend_resume_check=1

# Enables caliptra_ss_usb_device_wakeup_checker, which owns CHK_DEVICE_WAKEUP_K
# on the DUT UTMI outputs (TXValid high with linestate=K). This is the check
# this test exists for: it is the only observable that can distinguish a DUT
# that woke the bus by itself from one whose remote wakeup is dead. It is a
# separate plusarg from +usb_suspend_resume_check on purpose, because the
# global-suspend tests, where the HOST ends the suspend and the device never
# signals wakeup, must not inherit a check they are guaranteed to fail.
#
# The host-side VIP field svt_usb_status::device_remote_wakeup_in_progress is
# deliberately NOT used as the verdict; it was measured staying 0 through a
# full 3.089 ms device K. See docs/usb_remote_wakeup_selfclear_race_report.md
# sections 2A.4 and 7.4.
VCS_SIM_OPTS += +usb_device_wakeup_check=1
