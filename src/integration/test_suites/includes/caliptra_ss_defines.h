/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
// Separating these defines from 'defines.h' since that file is auto-generated
// when building the VeeR EL2 from the configuration script, and clobbers
// these manual additions.

#ifndef CALIPTRA_SS_DEFINES_H
  #define CALIPTRA_SS_DEFINES_H

#include "soc_address_map.h"
#include "css_mcu0_defines.h"


/* ---- MCI ---- */
#define STDOUT                    SOC_MCI_TOP_MCI_REG_DEBUG_OUT

/* ---- Interrupts ---- */
#define CSS_MCU0_VEER_INTR_VEC_MCI         1
#define CSS_MCU0_VEER_INTR_VEC_I3C         2
// Used to tie-off unused upper intr bits
#define CSS_MCU0_VEER_INTR_EXT_LSB         3

#define CSS_MCU0_VEER_INTR_PRIO_MCI        8
#define CSS_MCU0_VEER_INTR_PRIO_I3C        7


#endif // CALIPTRA_SS_DEFINES_H
