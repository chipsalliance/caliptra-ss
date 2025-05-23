<!-- SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
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
-->
## Generate `fuse_ctrl` Partitions

This script generates the configurable (register and partition) blocks for
the instantiation of the `fuse_ctrl`.

### Modus Operandi
The configurable parts of the `fuse_ctrl` are bootstrapped via several [Mako](https://www.makotemplates.org/)
template files found in `src/fuse_ctrl/templates`. A Mako template file intersperses constant
data (rendered unchanged) with its own DSL that operates on arbitrary data that is passed
as Python variables to the rendering function. Each template file is rendered into a
file of the same name without the `.tpl` suffix:

 - `otp_ctrl_mmap.hjson.tpl`: All the partitions and their corresponding fuses are defined
   in this template file. If a user wishes to add, remove or update a partition, it should
   happen in here. The template further contains a configurable portion with respect to
   vendor-specific partitions that is instrumented via `gen_fuse_ctrl_partitions.yml`
   (see below).
 - `otp_ctrl.hjson.tpl`: All the CSRs are defined in this template file. Since the exact
   composition of the register map depends on the defined partitions, the generated
   `otp_ctrl_mmap.hjson` serves as a basis for this template. If a user wishes to add,
   remove or update a register, it should happen in this file.
 - `otp_ctrl_pkg.sv.tpl`, `otp_ctrl_reg_top.sv.tpl`: These two template files are rendered
   into the register RTL. They depend on the generated `otp_ctrl.hjson` file and, under
   normal circumstances, should not be modified.
 - `otp_ctrl_part_pkg.sv.tpl`: A partition-specific RTL block is rendered from this
   template file for which the generated `otp_ctrl_mmap.hjson` serves as a basis.
   It should not be modified.
 - `otp_ctrl.rdl.tpl`: Unfortunately, there does not seem to exist a mature tool that
   converts OpenTitan register files, i.e., `otp_ctrl.hjson`, into a corresponding
   `RDL` file, hence any change to the register map in `otp_ctrl.hjson` must be
   duplicated to this file.

```
/*------------------------------+
 | gen_fuse_ctrl_partitions.yml |
 +------------------------------*/
    |     
    |     /*---------------------------+       /*----------------------------+
    ---- > | otp_ctrl_mmap.hjson(.tpl) | -----> | otp_ctrl_part_pkg.sv(.tpl) |
           +---------------------------*/       +----------------------------*/
                        |
                        |    /*----------------------+      /*--------------------+
                        ----> | otp_ctrl.hjson(.tpl) | ----> | otp_ctrl.rdl(.tpl) |
                              +----------------------*/      +--------------------*/
                                        |
    /*---------------------------+      |     /*---------------------------+
     | otp_ctrl_reg_top.sv(.tpl) | <---------> | otp_ctrl_reg_pkg.sv(.tpl) |
     +---------------------------*/            +---------------------------*/
```

The generated RTL and configuration files alongside their corresponding Markdown documentation files 
and placed in the following directories:

```
src/fuse_ctrl/rtl
├── otp_ctrl_part_pkg.sv
├── otp_ctrl_core_reg_top.sv
└── otp_ctrl_reg_pkg.sv
src/fuse_ctrl/data
├── otp_ctrl.rdl
├── otp_ctrl_mmap.hjson
└── otp_ctrl.hjson
src/fuse_ctrl/doc
├── otp_ctrl_digests.md
├── otp_ctrl_field_descriptions.md
├── otp_ctrl_mmap.md
└── otp_ctrl_partitions.md
```

### Vendor-Specific Partitions

Optional vendor-specific partitions with variable number of fuses can
be added by setting the following parameters in `gen_fuse_ctrl_partitions.yml`
to non-zero values:

 - `num_vendor_pk_fuses`: This will generate either up to three partitions pertaining
   to the public-key hashes:
   1. `VENDOR_HASHES_MANUF_PARTITION`: Contains the first vendor public-key hashe.
   Programmable during the manufacturing life-cycle phase.
   2. `VENDOR_HASHES_PROD_PARTITION`: Contains the remaining `num_pk_fuses-1` vendor public-key hashes.
   In-field programmable. This partition is omitted if `num_pk_fuses==1`.
   3. `VENDOR_REVOCATIONS_PROD_PARTITION`: Contains `num_pk_fuses` sets of revocation bits for each
    vendor public-key.
 - `num_vendor_secret_fuses`: If non-zero, this parameter will result in the following partition:
   1. `VENDOR_SECRET_PROD_PARTITION`: Contains `num_vendor_secret_fuses` secret vendor-specific fuses.
    In-field programmable.
 - `num_vendor_non_secret_fuses`: If non-zero, this parameter will result in the following partition:
   1. `VENDOR_NON_SECRET_PROD_PARTITION`: Contains `N` non-secret vendor-specific fuses.
    In-field programmable.

For the exact definition of these vendor-specific fuses see `otp_ctrl_mmap.hjson.tpl`.

### Execution
```sh
cd $CALIPTRA_SS_ROOT/tools/scripts/fuse_ctrl_script
cat requirements.txt
> hjson==3.1.0
> importlib_resources==5.4.0
> Mako==1.1.6
> pycryptodome==3.21.0
> PyYAML==6.0.1
> tabulate==0.8.10
python3 -m pip install -r requirements.txt
cd $CALIPTRA_SS_ROOT
./tools/scripts/fuse_ctrl_script/gen_fuse_ctrl_partitions.py -f tools/scripts/fuse_ctrl_script/gen_fuse_ctrl_partitions.yml
```

### Verification
Invalid edits to the `otp_ctrl_mmap.hjson.tpl` and `otp_ctrl.hjson.tpl` files are caught
and signaled to the user. Potential invalid configurations include:
  - Any kind of HJSON syntax error.
  - The partitions do not fit into the allocated memory.
  - Duplicated partition/fuse names.
  - Unknown partition parameters.
  - Undeclared keys for the secret partitions.
  - Missing fields such as register or fuse sizes.
