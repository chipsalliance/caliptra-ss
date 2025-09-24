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

// NOTE: This file is a header for fuse_ctrl_read_lock_map.c. That
//       file can only be compiled with SOC-level information (by
//       including soc_address_map.h).

#include <stdint.h>

// An array that maps from the ordered list of partitions with a read-lock CSR
// to the index of that partition in the "partitions" array defined in
// fuse_ctrl_mmap.c
//
// If there are N such partitions, this array will have N+1 elements and the
// last item (at address N) will have value UINT32_MAX.
extern const uint32_t read_lock_partition_indices[];

// An array that maps from the ordered list of partitions with a read-lock CSR
// to the address of that CSR.
//
// This array will have the same length as read_lock_partition_indices and will
// terminate with UINT32_MAX in the same way.
extern const uint32_t read_lock_csr_mapping[];
