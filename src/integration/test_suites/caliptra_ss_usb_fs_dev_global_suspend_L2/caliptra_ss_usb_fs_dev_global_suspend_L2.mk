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
# TESTNAME=caliptra_ss_usb_fs_dev_global_suspend_L2, so it cannot affect any
# other test.
#
# Enables caliptra_ss_usb_suspend_resume_checker.sv, which owns the DUT-side
# pass/fail condition for this test (UTMI SuspendM low then high again). The
# "=1" form is kept for consistency with the test yml; $test$plusargs matches
# on prefix, so the value itself is ignored. Without this the checker is inert
# and the test cannot fail on DUT behaviour.
VCS_SIM_OPTS += +usb_suspend_resume_check=1
