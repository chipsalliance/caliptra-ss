// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Nils Wistoff <nwistoff@iis.ee.ethz.ch>

// Macros to assign AXI Interfaces and Structs

`ifndef CALIPTRA_SS_TB_AXI_ASSIGN_SVH_
`define CALIPTRA_SS_TB_AXI_ASSIGN_SVH_

////////////////////////////////////////////////////////////////////////////////////////////////////
// Internal implementation for assigning one AXI struct or interface to another struct or interface.
// The path to the signals on each side is defined by the `__sep*` arguments.  The `__opt_as`
// argument allows to use this standalone (with `__opt_as = assign`) or in assignments inside
// processes (with `__opt_as` void).
`define CALIPTRA_SS_TB___AXI_TO_AW(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)   \
  __opt_as __lhs``__lhs_sep``id     = __rhs``__rhs_sep``id;         \
  __opt_as __lhs``__lhs_sep``addr   = __rhs``__rhs_sep``addr;       \
  __opt_as __lhs``__lhs_sep``len    = __rhs``__rhs_sep``len;        \
  __opt_as __lhs``__lhs_sep``size   = __rhs``__rhs_sep``size;       \
  __opt_as __lhs``__lhs_sep``burst  = __rhs``__rhs_sep``burst;      \
  __opt_as __lhs``__lhs_sep``lock   = __rhs``__rhs_sep``lock;       \
  __opt_as __lhs``__lhs_sep``cache  = __rhs``__rhs_sep``cache;      \
  __opt_as __lhs``__lhs_sep``prot   = __rhs``__rhs_sep``prot;       \
  __opt_as __lhs``__lhs_sep``qos    = __rhs``__rhs_sep``qos;        \
  __opt_as __lhs``__lhs_sep``region = __rhs``__rhs_sep``region;     \
  __opt_as __lhs``__lhs_sep``atop   = __rhs``__rhs_sep``atop;       \
  __opt_as __lhs``__lhs_sep``user   = __rhs``__rhs_sep``user;
`define CALIPTRA_SS_TB___AXI_TO_W(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)    \
  __opt_as __lhs``__lhs_sep``data   = __rhs``__rhs_sep``data;       \
  __opt_as __lhs``__lhs_sep``strb   = __rhs``__rhs_sep``strb;       \
  __opt_as __lhs``__lhs_sep``last   = __rhs``__rhs_sep``last;       \
  __opt_as __lhs``__lhs_sep``user   = __rhs``__rhs_sep``user;
`define CALIPTRA_SS_TB___AXI_TO_B(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)    \
  __opt_as __lhs``__lhs_sep``id     = __rhs``__rhs_sep``id;         \
  __opt_as __lhs``__lhs_sep``resp   = __rhs``__rhs_sep``resp;       \
  __opt_as __lhs``__lhs_sep``user   = __rhs``__rhs_sep``user;
`define CALIPTRA_SS_TB___AXI_TO_AR(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)   \
  __opt_as __lhs``__lhs_sep``id     = __rhs``__rhs_sep``id;         \
  __opt_as __lhs``__lhs_sep``addr   = __rhs``__rhs_sep``addr;       \
  __opt_as __lhs``__lhs_sep``len    = __rhs``__rhs_sep``len;        \
  __opt_as __lhs``__lhs_sep``size   = __rhs``__rhs_sep``size;       \
  __opt_as __lhs``__lhs_sep``burst  = __rhs``__rhs_sep``burst;      \
  __opt_as __lhs``__lhs_sep``lock   = __rhs``__rhs_sep``lock;       \
  __opt_as __lhs``__lhs_sep``cache  = __rhs``__rhs_sep``cache;      \
  __opt_as __lhs``__lhs_sep``prot   = __rhs``__rhs_sep``prot;       \
  __opt_as __lhs``__lhs_sep``qos    = __rhs``__rhs_sep``qos;        \
  __opt_as __lhs``__lhs_sep``region = __rhs``__rhs_sep``region;     \
  __opt_as __lhs``__lhs_sep``user   = __rhs``__rhs_sep``user;
`define CALIPTRA_SS_TB___AXI_TO_R(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)    \
  __opt_as __lhs``__lhs_sep``id     = __rhs``__rhs_sep``id;         \
  __opt_as __lhs``__lhs_sep``data   = __rhs``__rhs_sep``data;       \
  __opt_as __lhs``__lhs_sep``resp   = __rhs``__rhs_sep``resp;       \
  __opt_as __lhs``__lhs_sep``last   = __rhs``__rhs_sep``last;       \
  __opt_as __lhs``__lhs_sep``user   = __rhs``__rhs_sep``user;
`define CALIPTRA_SS_TB___AXI_TO_REQ(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)  \
  `CALIPTRA_SS_TB___AXI_TO_AW(__opt_as, __lhs.aw, __lhs_sep, __rhs.aw, __rhs_sep)  \
  __opt_as __lhs.aw_valid = __rhs.aw_valid;                         \
  `CALIPTRA_SS_TB___AXI_TO_W(__opt_as, __lhs.w, __lhs_sep, __rhs.w, __rhs_sep)     \
  __opt_as __lhs.w_valid = __rhs.w_valid;                           \
  __opt_as __lhs.b_ready = __rhs.b_ready;                           \
  `CALIPTRA_SS_TB___AXI_TO_AR(__opt_as, __lhs.ar, __lhs_sep, __rhs.ar, __rhs_sep)  \
  __opt_as __lhs.ar_valid = __rhs.ar_valid;                         \
  __opt_as __lhs.r_ready = __rhs.r_ready;
`define CALIPTRA_SS_TB___AXI_TO_RESP(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep) \
  __opt_as __lhs.aw_ready = __rhs.aw_ready;                         \
  __opt_as __lhs.ar_ready = __rhs.ar_ready;                         \
  __opt_as __lhs.w_ready = __rhs.w_ready;                           \
  __opt_as __lhs.b_valid = __rhs.b_valid;                           \
  `CALIPTRA_SS_TB___AXI_TO_B(__opt_as, __lhs.b, __lhs_sep, __rhs.b, __rhs_sep)     \
  __opt_as __lhs.r_valid = __rhs.r_valid;                           \
  `CALIPTRA_SS_TB___AXI_TO_R(__opt_as, __lhs.r, __lhs_sep, __rhs.r, __rhs_sep)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning one AXI4+ATOP interface to another, as if you would do `assign slv = mst;`
//
// The channel assignments `AXI_ASSIGN_XX(dst, src)` assign all payload and the valid signal of the
// `XX` channel from the `src` to the `dst` interface and they assign the ready signal from the
// `src` to the `dst` interface.
// The interface assignment `AXI_ASSIGN(dst, src)` assigns all channels including handshakes as if
// `src` was the master of `dst`.
//
// Usage Example:
// `AXI_ASSIGN(slv, mst)
// `AXI_ASSIGN_AW(dst, src)
// `AXI_ASSIGN_R(dst, src)
`define CALIPTRA_SS_TB_AXI_ASSIGN_AW(dst, src)               \
  `CALIPTRA_SS_TB___AXI_TO_AW(assign, dst.aw, _, src.aw, _)  \
  assign dst.aw_valid = src.aw_valid;         \
  assign src.aw_ready = dst.aw_ready;
`define CALIPTRA_SS_TB_AXI_ASSIGN_W(dst, src)                \
  `CALIPTRA_SS_TB___AXI_TO_W(assign, dst.w, _, src.w, _)     \
  assign dst.w_valid  = src.w_valid;          \
  assign src.w_ready  = dst.w_ready;
`define CALIPTRA_SS_TB_AXI_ASSIGN_B(dst, src)                \
  `CALIPTRA_SS_TB___AXI_TO_B(assign, dst.b, _, src.b, _)     \
  assign dst.b_valid  = src.b_valid;          \
  assign src.b_ready  = dst.b_ready;
`define CALIPTRA_SS_TB_AXI_ASSIGN_AR(dst, src)               \
  `CALIPTRA_SS_TB___AXI_TO_AR(assign, dst.ar, _, src.ar, _)  \
  assign dst.ar_valid = src.ar_valid;         \
  assign src.ar_ready = dst.ar_ready;
`define CALIPTRA_SS_TB_AXI_ASSIGN_R(dst, src)                \
  `CALIPTRA_SS_TB___AXI_TO_R(assign, dst.r, _, src.r, _)     \
  assign dst.r_valid  = src.r_valid;          \
  assign src.r_ready  = dst.r_ready;
`define CALIPTRA_SS_TB_AXI_ASSIGN(slv, mst)  \
  `CALIPTRA_SS_TB_AXI_ASSIGN_AW(slv, mst)    \
  `CALIPTRA_SS_TB_AXI_ASSIGN_W(slv, mst)     \
  `CALIPTRA_SS_TB_AXI_ASSIGN_B(mst, slv)     \
  `CALIPTRA_SS_TB_AXI_ASSIGN_AR(slv, mst)    \
  `CALIPTRA_SS_TB_AXI_ASSIGN_R(mst, slv)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning a AXI4+ATOP interface to a monitor modport, as if you would do `assign mon = axi_if;`
//
// The channel assignment `AXI_ASSIGN_MONITOR(mon_dv, axi_if)` assigns all signals from `axi_if`
// to the `mon_dv` interface.
//
// Usage Example:
// `AXI_ASSIGN_MONITOR(mon_dv, axi_if)
`define CALIPTRA_SS_TB_AXI_ASSIGN_MONITOR(mon_dv, axi_if)          \
  `CALIPTRA_SS_TB___AXI_TO_AW(assign, mon_dv.aw, _, axi_if.aw, _)  \
  assign mon_dv.aw_valid  = axi_if.aw_valid;        \
  assign mon_dv.aw_ready  = axi_if.aw_ready;        \
  `CALIPTRA_SS_TB___AXI_TO_W(assign, mon_dv.w, _, axi_if.w, _)     \
  assign mon_dv.w_valid   = axi_if.w_valid;         \
  assign mon_dv.w_ready   = axi_if.w_ready;         \
  `CALIPTRA_SS_TB___AXI_TO_B(assign, mon_dv.b, _, axi_if.b, _)     \
  assign mon_dv.b_valid   = axi_if.b_valid;         \
  assign mon_dv.b_ready   = axi_if.b_ready;         \
  `CALIPTRA_SS_TB___AXI_TO_AR(assign, mon_dv.ar, _, axi_if.ar, _)  \
  assign mon_dv.ar_valid  = axi_if.ar_valid;        \
  assign mon_dv.ar_ready  = axi_if.ar_ready;        \
  `CALIPTRA_SS_TB___AXI_TO_R(assign, mon_dv.r, _, axi_if.r, _)     \
  assign mon_dv.r_valid   = axi_if.r_valid;         \
  assign mon_dv.r_ready   = axi_if.r_ready;
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Setting an interface from channel or request/response structs inside a process.
//
// The channel macros `AXI_SET_FROM_XX(axi_if, xx_struct)` set the payload signals of the `axi_if`
// interface from the signals in `xx_struct`.  They do not set the handshake signals.
// The request macro `AXI_SET_FROM_REQ(axi_if, req_struct)` sets all request channels (AW, W, AR)
// and the request-side handshake signals (AW, W, and AR valid and B and R ready) of the `axi_if`
// interface from the signals in `req_struct`.
// The response macro `AXI_SET_FROM_RESP(axi_if, resp_struct)` sets both response channels (B and R)
// and the response-side handshake signals (B and R valid and AW, W, and AR ready) of the `axi_if`
// interface from the signals in `resp_struct`.
//
// Usage Example:
// always_comb begin
//   `AXI_SET_FROM_REQ(my_if, my_req_struct)
// end
`define CALIPTRA_SS_TB_AXI_SET_FROM_AW(axi_if, aw_struct)      `CALIPTRA_SS_TB___AXI_TO_AW(, axi_if.aw, _, aw_struct, .)
`define CALIPTRA_SS_TB_AXI_SET_FROM_W(axi_if, w_struct)        `CALIPTRA_SS_TB___AXI_TO_W(, axi_if.w, _, w_struct, .)
`define CALIPTRA_SS_TB_AXI_SET_FROM_B(axi_if, b_struct)        `CALIPTRA_SS_TB___AXI_TO_B(, axi_if.b, _, b_struct, .)
`define CALIPTRA_SS_TB_AXI_SET_FROM_AR(axi_if, ar_struct)      `CALIPTRA_SS_TB___AXI_TO_AR(, axi_if.ar, _, ar_struct, .)
`define CALIPTRA_SS_TB_AXI_SET_FROM_R(axi_if, r_struct)        `CALIPTRA_SS_TB___AXI_TO_R(, axi_if.r, _, r_struct, .)
`define CALIPTRA_SS_TB_AXI_SET_FROM_REQ(axi_if, req_struct)    `CALIPTRA_SS_TB___AXI_TO_REQ(, axi_if, _, req_struct, .)
`define CALIPTRA_SS_TB_AXI_SET_FROM_RESP(axi_if, resp_struct)  `CALIPTRA_SS_TB___AXI_TO_RESP(, axi_if, _, resp_struct, .)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning an interface from channel or request/response structs outside a process.
//
// The channel macros `AXI_ASSIGN_FROM_XX(axi_if, xx_struct)` assign the payload signals of the
// `axi_if` interface from the signals in `xx_struct`.  They do not assign the handshake signals.
// The request macro `AXI_ASSIGN_FROM_REQ(axi_if, req_struct)` assigns all request channels (AW, W,
// AR) and the request-side handshake signals (AW, W, and AR valid and B and R ready) of the
// `axi_if` interface from the signals in `req_struct`.
// The response macro `AXI_ASSIGN_FROM_RESP(axi_if, resp_struct)` assigns both response channels (B
// and R) and the response-side handshake signals (B and R valid and AW, W, and AR ready) of the
// `axi_if` interface from the signals in `resp_struct`.
//
// Usage Example:
// `AXI_ASSIGN_FROM_REQ(my_if, my_req_struct)
`define CALIPTRA_SS_TB_AXI_ASSIGN_FROM_AW(axi_if, aw_struct)     `CALIPTRA_SS_TB___AXI_TO_AW(assign, axi_if.aw, _, aw_struct, .)
`define CALIPTRA_SS_TB_AXI_ASSIGN_FROM_W(axi_if, w_struct)       `CALIPTRA_SS_TB___AXI_TO_W(assign, axi_if.w, _, w_struct, .)
`define CALIPTRA_SS_TB_AXI_ASSIGN_FROM_B(axi_if, b_struct)       `CALIPTRA_SS_TB___AXI_TO_B(assign, axi_if.b, _, b_struct, .)
`define CALIPTRA_SS_TB_AXI_ASSIGN_FROM_AR(axi_if, ar_struct)     `CALIPTRA_SS_TB___AXI_TO_AR(assign, axi_if.ar, _, ar_struct, .)
`define CALIPTRA_SS_TB_AXI_ASSIGN_FROM_R(axi_if, r_struct)       `CALIPTRA_SS_TB___AXI_TO_R(assign, axi_if.r, _, r_struct, .)
`define CALIPTRA_SS_TB_AXI_ASSIGN_FROM_REQ(axi_if, req_struct)   `CALIPTRA_SS_TB___AXI_TO_REQ(assign, axi_if, _, req_struct, .)
`define CALIPTRA_SS_TB_AXI_ASSIGN_FROM_RESP(axi_if, resp_struct) `CALIPTRA_SS_TB___AXI_TO_RESP(assign, axi_if, _, resp_struct, .)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Setting channel or request/response structs from an interface inside a process.
//
// The channel macros `AXI_SET_TO_XX(xx_struct, axi_if)` set the signals of `xx_struct` to the
// payload signals of that channel in the `axi_if` interface.  They do not set the handshake
// signals.
// The request macro `AXI_SET_TO_REQ(axi_if, req_struct)` sets all signals of `req_struct` (i.e.,
// request channel (AW, W, AR) payload and request-side handshake signals (AW, W, and AR valid and
// B and R ready)) to the signals in the `axi_if` interface.
// The response macro `AXI_SET_TO_RESP(axi_if, resp_struct)` sets all signals of `resp_struct`
// (i.e., response channel (B and R) payload and response-side handshake signals (B and R valid and
// AW, W, and AR ready)) to the signals in the `axi_if` interface.
//
// Usage Example:
// always_comb begin
//   `AXI_SET_TO_REQ(my_req_struct, my_if)
// end
`define CALIPTRA_SS_TB_AXI_SET_TO_AW(aw_struct, axi_if)     `CALIPTRA_SS_TB___AXI_TO_AW(, aw_struct, ., axi_if.aw, _)
`define CALIPTRA_SS_TB_AXI_SET_TO_W(w_struct, axi_if)       `CALIPTRA_SS_TB___AXI_TO_W(, w_struct, ., axi_if.w, _)
`define CALIPTRA_SS_TB_AXI_SET_TO_B(b_struct, axi_if)       `CALIPTRA_SS_TB___AXI_TO_B(, b_struct, ., axi_if.b, _)
`define CALIPTRA_SS_TB_AXI_SET_TO_AR(ar_struct, axi_if)     `CALIPTRA_SS_TB___AXI_TO_AR(, ar_struct, ., axi_if.ar, _)
`define CALIPTRA_SS_TB_AXI_SET_TO_R(r_struct, axi_if)       `CALIPTRA_SS_TB___AXI_TO_R(, r_struct, ., axi_if.r, _)
`define CALIPTRA_SS_TB_AXI_SET_TO_REQ(req_struct, axi_if)   `CALIPTRA_SS_TB___AXI_TO_REQ(, req_struct, ., axi_if, _)
`define CALIPTRA_SS_TB_AXI_SET_TO_RESP(resp_struct, axi_if) `CALIPTRA_SS_TB___AXI_TO_RESP(, resp_struct, ., axi_if, _)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning channel or request/response structs from an interface outside a process.
//
// The channel macros `AXI_ASSIGN_TO_XX(xx_struct, axi_if)` assign the signals of `xx_struct` to the
// payload signals of that channel in the `axi_if` interface.  They do not assign the handshake
// signals.
// The request macro `AXI_ASSIGN_TO_REQ(axi_if, req_struct)` assigns all signals of `req_struct`
// (i.e., request channel (AW, W, AR) payload and request-side handshake signals (AW, W, and AR
// valid and B and R ready)) to the signals in the `axi_if` interface.
// The response macro `AXI_ASSIGN_TO_RESP(axi_if, resp_struct)` assigns all signals of `resp_struct`
// (i.e., response channel (B and R) payload and response-side handshake signals (B and R valid and
// AW, W, and AR ready)) to the signals in the `axi_if` interface.
//
// Usage Example:
// `AXI_ASSIGN_TO_REQ(my_req_struct, my_if)
`define CALIPTRA_SS_TB_AXI_ASSIGN_TO_AW(aw_struct, axi_if)     `CALIPTRA_SS_TB___AXI_TO_AW(assign, aw_struct, ., axi_if.aw, _)
`define CALIPTRA_SS_TB_AXI_ASSIGN_TO_W(w_struct, axi_if)       `CALIPTRA_SS_TB___AXI_TO_W(assign, w_struct, ., axi_if.w, _)
`define CALIPTRA_SS_TB_AXI_ASSIGN_TO_B(b_struct, axi_if)       `CALIPTRA_SS_TB___AXI_TO_B(assign, b_struct, ., axi_if.b, _)
`define CALIPTRA_SS_TB_AXI_ASSIGN_TO_AR(ar_struct, axi_if)     `CALIPTRA_SS_TB___AXI_TO_AR(assign, ar_struct, ., axi_if.ar, _)
`define CALIPTRA_SS_TB_AXI_ASSIGN_TO_R(r_struct, axi_if)       `CALIPTRA_SS_TB___AXI_TO_R(assign, r_struct, ., axi_if.r, _)
`define CALIPTRA_SS_TB_AXI_ASSIGN_TO_REQ(req_struct, axi_if)   `CALIPTRA_SS_TB___AXI_TO_REQ(assign, req_struct, ., axi_if, _)
`define CALIPTRA_SS_TB_AXI_ASSIGN_TO_RESP(resp_struct, axi_if) `CALIPTRA_SS_TB___AXI_TO_RESP(assign, resp_struct, ., axi_if, _)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Setting channel or request/response structs from another struct inside a process.
//
// The channel macros `AXI_SET_XX_STRUCT(lhs, rhs)` set the fields of the `lhs` channel struct to
// the fields of the `rhs` channel struct.  They do not set the handshake signals, which are not
// part of channel structs.
// The request macro `AXI_SET_REQ_STRUCT(lhs, rhs)` sets all fields of the `lhs` request struct to
// the fields of the `rhs` request struct.  This includes all request channel (AW, W, AR) payload
// and request-side handshake signals (AW, W, and AR valid and B and R ready).
// The response macro `AXI_SET_RESP_STRUCT(lhs, rhs)` sets all fields of the `lhs` response struct
// to the fields of the `rhs` response struct.  This includes all response channel (B and R) payload
// and response-side handshake signals (B and R valid and AW, W, and R ready).
//
// Usage Example:
// always_comb begin
//   `AXI_SET_REQ_STRUCT(my_req_struct, another_req_struct)
// end
`define CALIPTRA_SS_TB_AXI_SET_AW_STRUCT(lhs, rhs)     `CALIPTRA_SS_TB___AXI_TO_AW(, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_SET_W_STRUCT(lhs, rhs)       `CALIPTRA_SS_TB___AXI_TO_W(, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_SET_B_STRUCT(lhs, rhs)       `CALIPTRA_SS_TB___AXI_TO_B(, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_SET_AR_STRUCT(lhs, rhs)     `CALIPTRA_SS_TB___AXI_TO_AR(, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_SET_R_STRUCT(lhs, rhs)       `CALIPTRA_SS_TB___AXI_TO_R(, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_SET_REQ_STRUCT(lhs, rhs)   `CALIPTRA_SS_TB___AXI_TO_REQ(, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_SET_RESP_STRUCT(lhs, rhs) `CALIPTRA_SS_TB___AXI_TO_RESP(, lhs, ., rhs, .)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning channel or request/response structs from another struct outside a process.
//
// The channel macros `AXI_ASSIGN_XX_STRUCT(lhs, rhs)` assign the fields of the `lhs` channel struct
// to the fields of the `rhs` channel struct.  They do not assign the handshake signals, which are
// not part of the channel structs.
// The request macro `AXI_ASSIGN_REQ_STRUCT(lhs, rhs)` assigns all fields of the `lhs` request
// struct to the fields of the `rhs` request struct.  This includes all request channel (AW, W, AR)
// payload and request-side handshake signals (AW, W, and AR valid and B and R ready).
// The response macro `AXI_ASSIGN_RESP_STRUCT(lhs, rhs)` assigns all fields of the `lhs` response
// struct to the fields of the `rhs` response struct.  This includes all response channel (B and R)
// payload and response-side handshake signals (B and R valid and AW, W, and R ready).
//
// Usage Example:
// `AXI_ASSIGN_REQ_STRUCT(my_req_struct, another_req_struct)
`define CALIPTRA_SS_TB_AXI_ASSIGN_AW_STRUCT(lhs, rhs)     `CALIPTRA_SS_TB___AXI_TO_AW(assign, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_ASSIGN_W_STRUCT(lhs, rhs)       `CALIPTRA_SS_TB___AXI_TO_W(assign, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_ASSIGN_B_STRUCT(lhs, rhs)       `CALIPTRA_SS_TB___AXI_TO_B(assign, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_ASSIGN_AR_STRUCT(lhs, rhs)     `CALIPTRA_SS_TB___AXI_TO_AR(assign, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_ASSIGN_R_STRUCT(lhs, rhs)       `CALIPTRA_SS_TB___AXI_TO_R(assign, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_ASSIGN_REQ_STRUCT(lhs, rhs)   `CALIPTRA_SS_TB___AXI_TO_REQ(assign, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_ASSIGN_RESP_STRUCT(lhs, rhs) `CALIPTRA_SS_TB___AXI_TO_RESP(assign, lhs, ., rhs, .)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Internal implementation for assigning one Lite structs or interface to another struct or
// interface.  The path to the signals on each side is defined by the `__sep*` arguments.  The
// `__opt_as` argument allows to use this standalne (with `__opt_as = assign`) or in assignments
// inside processes (with `__opt_as` void).
`define CALIPTRA_SS_TB___AXI_LITE_TO_AX(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)  \
  __opt_as __lhs``__lhs_sep``addr = __rhs``__rhs_sep``addr;             \
  __opt_as __lhs``__lhs_sep``prot = __rhs``__rhs_sep``prot;
`define CALIPTRA_SS_TB___AXI_LITE_TO_W(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep) \
  __opt_as __lhs``__lhs_sep``data = __rhs``__rhs_sep``data;           \
  __opt_as __lhs``__lhs_sep``strb = __rhs``__rhs_sep``strb;
`define CALIPTRA_SS_TB___AXI_LITE_TO_B(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep) \
  __opt_as __lhs``__lhs_sep``resp = __rhs``__rhs_sep``resp;
`define CALIPTRA_SS_TB___AXI_LITE_TO_R(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep) \
  __opt_as __lhs``__lhs_sep``data = __rhs``__rhs_sep``data;           \
  __opt_as __lhs``__lhs_sep``resp = __rhs``__rhs_sep``resp;
`define CALIPTRA_SS_TB___AXI_LITE_TO_REQ(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep) \
  `CALIPTRA_SS_TB___AXI_LITE_TO_AX(__opt_as, __lhs.aw, __lhs_sep, __rhs.aw, __rhs_sep) \
  __opt_as __lhs.aw_valid = __rhs.aw_valid;                             \
  `CALIPTRA_SS_TB___AXI_LITE_TO_W(__opt_as, __lhs.w, __lhs_sep, __rhs.w, __rhs_sep)    \
  __opt_as __lhs.w_valid = __rhs.w_valid;                               \
  __opt_as __lhs.b_ready = __rhs.b_ready;                               \
  `CALIPTRA_SS_TB___AXI_LITE_TO_AX(__opt_as, __lhs.ar, __lhs_sep, __rhs.ar, __rhs_sep) \
  __opt_as __lhs.ar_valid = __rhs.ar_valid;                             \
  __opt_as __lhs.r_ready = __rhs.r_ready;
`define CALIPTRA_SS_TB___AXI_LITE_TO_RESP(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)  \
  __opt_as __lhs.aw_ready = __rhs.aw_ready;                               \
  __opt_as __lhs.ar_ready = __rhs.ar_ready;                               \
  __opt_as __lhs.w_ready = __rhs.w_ready;                                 \
  __opt_as __lhs.b_valid = __rhs.b_valid;                                 \
  `CALIPTRA_SS_TB___AXI_LITE_TO_B(__opt_as, __lhs.b, __lhs_sep, __rhs.b, __rhs_sep)      \
  __opt_as __lhs.r_valid = __rhs.r_valid;                                 \
  `CALIPTRA_SS_TB___AXI_LITE_TO_R(__opt_as, __lhs.r, __lhs_sep, __rhs.r, __rhs_sep)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning one AXI-Lite interface to another, as if you would do `assign slv = mst;`
//
// The channel assignments `AXI_LITE_ASSIGN_XX(dst, src)` assign all payload and the valid signal of
// the `XX` channel from the `src` to the `dst` interface and they assign the ready signal from the
// `src` to the `dst` interface.
// The interface assignment `AXI_LITE_ASSIGN(dst, src)` assigns all channels including handshakes as
// if `src` was the master of `dst`.
//
// Usage Example:
// `AXI_LITE_ASSIGN(slv, mst)
// `AXI_LITE_ASSIGN_AW(dst, src)
// `AXI_LITE_ASSIGN_R(dst, src)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_AW(dst, src)              \
  `CALIPTRA_SS_TB___AXI_LITE_TO_AX(assign, dst.aw, _, src.aw, _) \
  assign dst.aw_valid = src.aw_valid;             \
  assign src.aw_ready = dst.aw_ready;
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_W(dst, src)             \
  `CALIPTRA_SS_TB___AXI_LITE_TO_W(assign, dst.w, _, src.w, _)  \
  assign dst.w_valid  = src.w_valid;            \
  assign src.w_ready  = dst.w_ready;
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_B(dst, src)             \
  `CALIPTRA_SS_TB___AXI_LITE_TO_B(assign, dst.b, _, src.b, _)  \
  assign dst.b_valid  = src.b_valid;            \
  assign src.b_ready  = dst.b_ready;
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_AR(dst, src)              \
  `CALIPTRA_SS_TB___AXI_LITE_TO_AX(assign, dst.ar, _, src.ar, _) \
  assign dst.ar_valid = src.ar_valid;             \
  assign src.ar_ready = dst.ar_ready;
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_R(dst, src)             \
  `CALIPTRA_SS_TB___AXI_LITE_TO_R(assign, dst.r, _, src.r, _)  \
  assign dst.r_valid  = src.r_valid;            \
  assign src.r_ready  = dst.r_ready;
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN(slv, mst) \
  `CALIPTRA_SS_TB_AXI_LITE_ASSIGN_AW(slv, mst)   \
  `CALIPTRA_SS_TB_AXI_LITE_ASSIGN_W(slv, mst)    \
  `CALIPTRA_SS_TB_AXI_LITE_ASSIGN_B(mst, slv)    \
  `CALIPTRA_SS_TB_AXI_LITE_ASSIGN_AR(slv, mst)   \
  `CALIPTRA_SS_TB_AXI_LITE_ASSIGN_R(mst, slv)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Setting a Lite interface from channel or request/response structs inside a process.
//
// The channel macros `AXI_LITE_SET_FROM_XX(axi_if, xx_struct)` set the payload signals of the
// `axi_if` interface from the signals in `xx_struct`.  They do not set the handshake signals.
// The request macro `AXI_LITE_SET_FROM_REQ(axi_if, req_struct)` sets all request channels (AW, W,
// AR) and the request-side handshake signals (AW, W, and AR valid and B and R ready) of the
// `axi_if` interface from the signals in `req_struct`.
// The response macro `AXI_LITE_SET_FROM_RESP(axi_if, resp_struct)` sets both response channels (B
// and R) and the response-side handshake signals (B and R valid and AW, W, and AR ready) of the
// `axi_if` interface from the signals in `resp_struct`.
//
// Usage Example:
// always_comb begin
//   `AXI_LITE_SET_FROM_REQ(my_if, my_req_struct)
// end
`define CALIPTRA_SS_TB_AXI_LITE_SET_FROM_AW(axi_if, aw_struct)      `CALIPTRA_SS_TB___AXI_LITE_TO_AX(, axi_if.aw, _, aw_struct, .)
`define CALIPTRA_SS_TB_AXI_LITE_SET_FROM_W(axi_if, w_struct)        `CALIPTRA_SS_TB___AXI_LITE_TO_W(, axi_if.w, _, w_struct, .)
`define CALIPTRA_SS_TB_AXI_LITE_SET_FROM_B(axi_if, b_struct)        `CALIPTRA_SS_TB___AXI_LITE_TO_B(, axi_if.b, _, b_struct, .)
`define CALIPTRA_SS_TB_AXI_LITE_SET_FROM_AR(axi_if, ar_struct)      `CALIPTRA_SS_TB___AXI_LITE_TO_AX(, axi_if.ar, _, ar_struct, .)
`define CALIPTRA_SS_TB_AXI_LITE_SET_FROM_R(axi_if, r_struct)        `CALIPTRA_SS_TB___AXI_LITE_TO_R(, axi_if.r, _, r_struct, .)
`define CALIPTRA_SS_TB_AXI_LITE_SET_FROM_REQ(axi_if, req_struct)    `CALIPTRA_SS_TB___AXI_LITE_TO_REQ(, axi_if, _, req_struct, .)
`define CALIPTRA_SS_TB_AXI_LITE_SET_FROM_RESP(axi_if, resp_struct)  `CALIPTRA_SS_TB___AXI_LITE_TO_RESP(, axi_if, _, resp_struct, .)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning a Lite interface from channel or request/response structs outside a process.
//
// The channel macros `AXI_LITE_ASSIGN_FROM_XX(axi_if, xx_struct)` assign the payload signals of the
// `axi_if` interface from the signals in `xx_struct`.  They do not assign the handshake signals.
// The request macro `AXI_LITE_ASSIGN_FROM_REQ(axi_if, req_struct)` assigns all request channels
// (AW, W, AR) and the request-side handshake signals (AW, W, and AR valid and B and R ready) of the
// `axi_if` interface from the signals in `req_struct`.
// The response macro `AXI_LITE_ASSIGN_FROM_RESP(axi_if, resp_struct)` assigns both response
// channels (B and R) and the response-side handshake signals (B and R valid and AW, W, and AR
// ready) of the `axi_if` interface from the signals in `resp_struct`.
//
// Usage Example:
// `AXI_LITE_ASSIGN_FROM_REQ(my_if, my_req_struct)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_FROM_AW(axi_if, aw_struct)     `CALIPTRA_SS_TB___AXI_LITE_TO_AX(assign, axi_if.aw, _, aw_struct, .)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_FROM_W(axi_if, w_struct)       `CALIPTRA_SS_TB___AXI_LITE_TO_W(assign, axi_if.w, _, w_struct, .)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_FROM_B(axi_if, b_struct)       `CALIPTRA_SS_TB___AXI_LITE_TO_B(assign, axi_if.b, _, b_struct, .)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_FROM_AR(axi_if, ar_struct)     `CALIPTRA_SS_TB___AXI_LITE_TO_AX(assign, axi_if.ar, _, ar_struct, .)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_FROM_R(axi_if, r_struct)       `CALIPTRA_SS_TB___AXI_LITE_TO_R(assign, axi_if.r, _, r_struct, .)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_FROM_REQ(axi_if, req_struct)   `CALIPTRA_SS_TB___AXI_LITE_TO_REQ(assign, axi_if, _, req_struct, .)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_FROM_RESP(axi_if, resp_struct) `CALIPTRA_SS_TB___AXI_LITE_TO_RESP(assign, axi_if, _, resp_struct, .)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Setting channel or request/response structs from an interface inside a process.
//
// The channel macros `AXI_LITE_SET_TO_XX(xx_struct, axi_if)` set the signals of `xx_struct` to the
// payload signals of that channel in the `axi_if` interface.  They do not set the handshake
// signals.
// The request macro `AXI_LITE_SET_TO_REQ(axi_if, req_struct)` sets all signals of `req_struct`
// (i.e., request channel (AW, W, AR) payload and request-side handshake signals (AW, W, and AR
// valid and B and R ready)) to the signals in the `axi_if` interface.
// The response macro `AXI_LITE_SET_TO_RESP(axi_if, resp_struct)` sets all signals of `resp_struct`
// (i.e., response channel (B and R) payload and response-side handshake signals (B and R valid and
// AW, W, and AR ready)) to the signals in the `axi_if` interface.
//
// Usage Example:
// always_comb begin
//   `AXI_LITE_SET_TO_REQ(my_req_struct, my_if)
// end
`define CALIPTRA_SS_TB_AXI_LITE_SET_TO_AW(aw_struct, axi_if)     `CALIPTRA_SS_TB___AXI_LITE_TO_AX(, aw_struct, ., axi_if.aw, _)
`define CALIPTRA_SS_TB_AXI_LITE_SET_TO_W(w_struct, axi_if)       `CALIPTRA_SS_TB___AXI_LITE_TO_W(, w_struct, ., axi_if.w, _)
`define CALIPTRA_SS_TB_AXI_LITE_SET_TO_B(b_struct, axi_if)       `CALIPTRA_SS_TB___AXI_LITE_TO_B(, b_struct, ., axi_if.b, _)
`define CALIPTRA_SS_TB_AXI_LITE_SET_TO_AR(ar_struct, axi_if)     `CALIPTRA_SS_TB___AXI_LITE_TO_AX(, ar_struct, ., axi_if.ar, _)
`define CALIPTRA_SS_TB_AXI_LITE_SET_TO_R(r_struct, axi_if)       `CALIPTRA_SS_TB___AXI_LITE_TO_R(, r_struct, ., axi_if.r, _)
`define CALIPTRA_SS_TB_AXI_LITE_SET_TO_REQ(req_struct, axi_if)   `CALIPTRA_SS_TB___AXI_LITE_TO_REQ(, req_struct, ., axi_if, _)
`define CALIPTRA_SS_TB_AXI_LITE_SET_TO_RESP(resp_struct, axi_if) `CALIPTRA_SS_TB___AXI_LITE_TO_RESP(, resp_struct, ., axi_if, _)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning channel or request/response structs from an interface outside a process.
//
// The channel macros `AXI_LITE_ASSIGN_TO_XX(xx_struct, axi_if)` assign the signals of `xx_struct`
// to the payload signals of that channel in the `axi_if` interface.  They do not assign the
// handshake signals.
// The request macro `AXI_LITE_ASSIGN_TO_REQ(axi_if, req_struct)` assigns all signals of
// `req_struct` (i.e., request channel (AW, W, AR) payload and request-side handshake signals (AW,
// W, and AR valid and B and R ready)) to the signals in the `axi_if` interface.
// The response macro `AXI_LITE_ASSIGN_TO_RESP(axi_if, resp_struct)` assigns all signals of
// `resp_struct` (i.e., response channel (B and R) payload and response-side handshake signals (B
// and R valid and AW, W, and AR ready)) to the signals in the `axi_if` interface.
//
// Usage Example:
// `AXI_LITE_ASSIGN_TO_REQ(my_req_struct, my_if)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_TO_AW(aw_struct, axi_if)     `CALIPTRA_SS_TB___AXI_LITE_TO_AX(assign, aw_struct, ., axi_if.aw, _)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_TO_W(w_struct, axi_if)       `CALIPTRA_SS_TB___AXI_LITE_TO_W(assign, w_struct, ., axi_if.w, _)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_TO_B(b_struct, axi_if)       `CALIPTRA_SS_TB___AXI_LITE_TO_B(assign, b_struct, ., axi_if.b, _)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_TO_AR(ar_struct, axi_if)     `CALIPTRA_SS_TB___AXI_LITE_TO_AX(assign, ar_struct, ., axi_if.ar, _)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_TO_R(r_struct, axi_if)       `CALIPTRA_SS_TB___AXI_LITE_TO_R(assign, r_struct, ., axi_if.r, _)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_TO_REQ(req_struct, axi_if)   `CALIPTRA_SS_TB___AXI_LITE_TO_REQ(assign, req_struct, ., axi_if, _)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_TO_RESP(resp_struct, axi_if) `CALIPTRA_SS_TB___AXI_LITE_TO_RESP(assign, resp_struct, ., axi_if, _)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Setting channel or request/response structs from another struct inside a process.
//
// The channel macros `AXI_LITE_SET_XX_STRUCT(lhs, rhs)` set the fields of the `lhs` channel struct
// to the fields of the `rhs` channel struct.  They do not set the handshake signals, which are not
// part of channel structs.
// The request macro `AXI_LITE_SET_REQ_STRUCT(lhs, rhs)` sets all fields of the `lhs` request struct
// to the fields of the `rhs` request struct.  This includes all request channel (AW, W, AR) payload
// and request-side handshake signals (AW, W, and AR valid and B and R ready).
// The response macro `AXI_LITE_SET_RESP_STRUCT(lhs, rhs)` sets all fields of the `lhs` response
// struct to the fields of the `rhs` response struct.  This includes all response channel (B and R)
// payload and response-side handshake signals (B and R valid and AW, W, and R ready).
//
// Usage Example:
// always_comb begin
//   `AXI_LITE_SET_REQ_STRUCT(my_req_struct, another_req_struct)
// end
`define CALIPTRA_SS_TB_AXI_LITE_SET_AW_STRUCT(lhs, rhs)     `CALIPTRA_SS_TB___AXI_LITE_TO_AX(, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_LITE_SET_W_STRUCT(lhs, rhs)       `CALIPTRA_SS_TB___AXI_LITE_TO_W(, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_LITE_SET_B_STRUCT(lhs, rhs)       `CALIPTRA_SS_TB___AXI_LITE_TO_B(, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_LITE_SET_AR_STRUCT(lhs, rhs)     `CALIPTRA_SS_TB___AXI_LITE_TO_AX(, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_LITE_SET_R_STRUCT(lhs, rhs)       `CALIPTRA_SS_TB___AXI_LITE_TO_R(, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_LITE_SET_REQ_STRUCT(lhs, rhs)   `CALIPTRA_SS_TB___AXI_LITE_TO_REQ(, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_LITE_SET_RESP_STRUCT(lhs, rhs) `CALIPTRA_SS_TB___AXI_LITE_TO_RESP(, lhs, ., rhs, .)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning channel or request/response structs from another struct outside a process.
//
// The channel macros `AXI_LITE_ASSIGN_XX_STRUCT(lhs, rhs)` assign the fields of the `lhs` channel
// struct to the fields of the `rhs` channel struct.  They do not assign the handshake signals,
// which are not part of the channel structs.
// The request macro `AXI_LITE_ASSIGN_REQ_STRUCT(lhs, rhs)` assigns all fields of the `lhs` request
// struct to the fields of the `rhs` request struct.  This includes all request channel (AW, W, AR)
// payload and request-side handshake signals (AW, W, and AR valid and B and R ready).
// The response macro `AXI_LITE_ASSIGN_RESP_STRUCT(lhs, rhs)` assigns all fields of the `lhs`
// response struct to the fields of the `rhs` response struct.  This includes all response channel
// (B and R) payload and response-side handshake signals (B and R valid and AW, W, and R ready).
//
// Usage Example:
// `AXI_LITE_ASSIGN_REQ_STRUCT(my_req_struct, another_req_struct)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_AW_STRUCT(lhs, rhs)     `CALIPTRA_SS_TB___AXI_LITE_TO_AX(assign, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_W_STRUCT(lhs, rhs)       `CALIPTRA_SS_TB___AXI_LITE_TO_W(assign, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_B_STRUCT(lhs, rhs)       `CALIPTRA_SS_TB___AXI_LITE_TO_B(assign, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_AR_STRUCT(lhs, rhs)     `CALIPTRA_SS_TB___AXI_LITE_TO_AX(assign, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_R_STRUCT(lhs, rhs)       `CALIPTRA_SS_TB___AXI_LITE_TO_R(assign, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_REQ_STRUCT(lhs, rhs)   `CALIPTRA_SS_TB___AXI_LITE_TO_REQ(assign, lhs, ., rhs, .)
`define CALIPTRA_SS_TB_AXI_LITE_ASSIGN_RESP_STRUCT(lhs, rhs) `CALIPTRA_SS_TB___AXI_LITE_TO_RESP(assign, lhs, ., rhs, .)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Macros for assigning flattened AXI ports to req/resp AXI structs
// Flat AXI ports are required by the Vivado IP Integrator. Vivado naming convention is followed.
//
// Usage Example:
// `AXI_ASSIGN_MASTER_TO_FLAT("my_bus", my_req_struct, my_rsp_struct)
`define CALIPTRA_SS_TB_AXI_ASSIGN_MASTER_TO_FLAT(pat, req, rsp) \
  assign m_axi_``pat``_awvalid  = req.aw_valid;  \
  assign m_axi_``pat``_awid     = req.aw.id;     \
  assign m_axi_``pat``_awaddr   = req.aw.addr;   \
  assign m_axi_``pat``_awlen    = req.aw.len;    \
  assign m_axi_``pat``_awsize   = req.aw.size;   \
  assign m_axi_``pat``_awburst  = req.aw.burst;  \
  assign m_axi_``pat``_awlock   = req.aw.lock;   \
  assign m_axi_``pat``_awcache  = req.aw.cache;  \
  assign m_axi_``pat``_awprot   = req.aw.prot;   \
  assign m_axi_``pat``_awqos    = req.aw.qos;    \
  assign m_axi_``pat``_awregion = req.aw.region; \
  assign m_axi_``pat``_awuser   = req.aw.user;   \
                                                 \
  assign m_axi_``pat``_wvalid   = req.w_valid;   \
  assign m_axi_``pat``_wdata    = req.w.data;    \
  assign m_axi_``pat``_wstrb    = req.w.strb;    \
  assign m_axi_``pat``_wlast    = req.w.last;    \
  assign m_axi_``pat``_wuser    = req.w.user;    \
                                                 \
  assign m_axi_``pat``_bready   = req.b_ready;   \
                                                 \
  assign m_axi_``pat``_arvalid  = req.ar_valid;  \
  assign m_axi_``pat``_arid     = req.ar.id;     \
  assign m_axi_``pat``_araddr   = req.ar.addr;   \
  assign m_axi_``pat``_arlen    = req.ar.len;    \
  assign m_axi_``pat``_arsize   = req.ar.size;   \
  assign m_axi_``pat``_arburst  = req.ar.burst;  \
  assign m_axi_``pat``_arlock   = req.ar.lock;   \
  assign m_axi_``pat``_arcache  = req.ar.cache;  \
  assign m_axi_``pat``_arprot   = req.ar.prot;   \
  assign m_axi_``pat``_arqos    = req.ar.qos;    \
  assign m_axi_``pat``_arregion = req.ar.region; \
  assign m_axi_``pat``_aruser   = req.ar.user;   \
                                                 \
  assign m_axi_``pat``_rready   = req.r_ready;   \
                                                 \
  assign rsp.aw_ready = m_axi_``pat``_awready;   \
  assign rsp.ar_ready = m_axi_``pat``_arready;   \
  assign rsp.w_ready  = m_axi_``pat``_wready;    \
                                                 \
  assign rsp.b_valid  = m_axi_``pat``_bvalid;    \
  assign rsp.b.id     = m_axi_``pat``_bid;       \
  assign rsp.b.resp   = m_axi_``pat``_bresp;     \
  assign rsp.b.user   = m_axi_``pat``_buser;     \
                                                 \
  assign rsp.r_valid  = m_axi_``pat``_rvalid;    \
  assign rsp.r.id     = m_axi_``pat``_rid;       \
  assign rsp.r.data   = m_axi_``pat``_rdata;     \
  assign rsp.r.resp   = m_axi_``pat``_rresp;     \
  assign rsp.r.last   = m_axi_``pat``_rlast;     \
  assign rsp.r.user   = m_axi_``pat``_ruser;

`define CALIPTRA_SS_TB_AXI_ASSIGN_SLAVE_TO_FLAT(pat, req, rsp)  \
  assign req.aw_valid  = s_axi_``pat``_awvalid;  \
  assign req.aw.id     = s_axi_``pat``_awid;     \
  assign req.aw.addr   = s_axi_``pat``_awaddr;   \
  assign req.aw.len    = s_axi_``pat``_awlen;    \
  assign req.aw.size   = s_axi_``pat``_awsize;   \
  assign req.aw.burst  = s_axi_``pat``_awburst;  \
  assign req.aw.lock   = s_axi_``pat``_awlock;   \
  assign req.aw.cache  = s_axi_``pat``_awcache;  \
  assign req.aw.prot   = s_axi_``pat``_awprot;   \
  assign req.aw.qos    = s_axi_``pat``_awqos;    \
  assign req.aw.region = s_axi_``pat``_awregion; \
  assign req.aw.user   = s_axi_``pat``_awuser;   \
                                                 \
  assign req.w_valid   = s_axi_``pat``_wvalid;   \
  assign req.w.data    = s_axi_``pat``_wdata;    \
  assign req.w.strb    = s_axi_``pat``_wstrb;    \
  assign req.w.last    = s_axi_``pat``_wlast;    \
  assign req.w.user    = s_axi_``pat``_wuser;    \
                                                 \
  assign req.b_ready   = s_axi_``pat``_bready;   \
                                                 \
  assign req.ar_valid  = s_axi_``pat``_arvalid;  \
  assign req.ar.id     = s_axi_``pat``_arid;     \
  assign req.ar.addr   = s_axi_``pat``_araddr;   \
  assign req.ar.len    = s_axi_``pat``_arlen;    \
  assign req.ar.size   = s_axi_``pat``_arsize;   \
  assign req.ar.burst  = s_axi_``pat``_arburst;  \
  assign req.ar.lock   = s_axi_``pat``_arlock;   \
  assign req.ar.cache  = s_axi_``pat``_arcache;  \
  assign req.ar.prot   = s_axi_``pat``_arprot;   \
  assign req.ar.qos    = s_axi_``pat``_arqos;    \
  assign req.ar.region = s_axi_``pat``_arregion; \
  assign req.ar.user   = s_axi_``pat``_aruser;   \
                                                 \
  assign req.r_ready   = s_axi_``pat``_rready;   \
                                                 \
  assign s_axi_``pat``_awready = rsp.aw_ready;   \
  assign s_axi_``pat``_arready = rsp.ar_ready;   \
  assign s_axi_``pat``_wready  = rsp.w_ready;    \
                                                 \
  assign s_axi_``pat``_bvalid  = rsp.b_valid;    \
  assign s_axi_``pat``_bid     = rsp.b.id;       \
  assign s_axi_``pat``_bresp   = rsp.b.resp;     \
  assign s_axi_``pat``_buser   = rsp.b.user;     \
                                                 \
  assign s_axi_``pat``_rvalid  = rsp.r_valid;    \
  assign s_axi_``pat``_rid     = rsp.r.id;       \
  assign s_axi_``pat``_rdata   = rsp.r.data;     \
  assign s_axi_``pat``_rresp   = rsp.r.resp;     \
  assign s_axi_``pat``_rlast   = rsp.r.last;     \
  assign s_axi_``pat``_ruser   = rsp.r.user;

`define CALIPTRA_SS_TB_AXI_ASSIGN_TO_FLAT_PORT(pat, req, rsp)  \
  .``pat``_awvalid  ( req.aw_valid  ), \
  .``pat``_awid     ( req.aw.id     ), \
  .``pat``_awaddr   ( req.aw.addr   ), \
  .``pat``_awlen    ( req.aw.len    ), \
  .``pat``_awsize   ( req.aw.size   ), \
  .``pat``_awburst  ( req.aw.burst  ), \
  .``pat``_awlock   ( req.aw.lock   ), \
  .``pat``_awcache  ( req.aw.cache  ), \
  .``pat``_awprot   ( req.aw.prot   ), \
  .``pat``_awqos    ( req.aw.qos    ), \
  .``pat``_awregion ( req.aw.region ), \
  .``pat``_awuser   ( req.aw.user   ), \
                                       \
  .``pat``_wvalid   ( req.w_valid   ), \
  .``pat``_wdata    ( req.w.data    ), \
  .``pat``_wstrb    ( req.w.strb    ), \
  .``pat``_wlast    ( req.w.last    ), \
  .``pat``_wuser    ( req.w.user    ), \
                                       \
  .``pat``_bready   ( req.b_ready   ), \
                                       \
  .``pat``_arvalid  ( req.ar_valid  ), \
  .``pat``_arid     ( req.ar.id     ), \
  .``pat``_araddr   ( req.ar.addr   ), \
  .``pat``_arlen    ( req.ar.len    ), \
  .``pat``_arsize   ( req.ar.size   ), \
  .``pat``_arburst  ( req.ar.burst  ), \
  .``pat``_arlock   ( req.ar.lock   ), \
  .``pat``_arcache  ( req.ar.cache  ), \
  .``pat``_arprot   ( req.ar.prot   ), \
  .``pat``_arqos    ( req.ar.qos    ), \
  .``pat``_arregion ( req.ar.region ), \
  .``pat``_aruser   ( req.ar.user   ), \
                                       \
  .``pat``_rready   ( req.r_ready   ), \
                                       \
  .``pat``_awready  ( rsp.aw_ready  ), \
  .``pat``_arready  ( rsp.ar_ready  ), \
  .``pat``_wready   ( rsp.w_ready   ), \
                                       \
  .``pat``_bvalid   ( rsp.b_valid   ), \
  .``pat``_bid      ( rsp.b.id      ), \
  .``pat``_bresp    ( rsp.b.resp    ), \
  .``pat``_buser    ( rsp.b.user    ), \
                                       \
  .``pat``_rvalid   ( rsp.r_valid   ), \
  .``pat``_rid      ( rsp.r.id      ), \
  .``pat``_rdata    ( rsp.r.data    ), \
  .``pat``_rresp    ( rsp.r.resp    ), \
  .``pat``_rlast    ( rsp.r.last    ), \
  .``pat``_ruser    ( rsp.r.user    )

`define CALIPTRA_SS_TB_AXI_ASSIGN_MASTER_TO_FLAT_PORT(name, req, rsp) \
  `CALIPTRA_SS_TB_AXI_ASSIGN_TO_FLAT_PORT(m_axi_``name``, req, rsp)

`define CALIPTRA_SS_TB_AXI_ASSIGN_SLAVE_TO_FLAT_PORT(name, req, rsp) \
  `CALIPTRA_SS_TB_AXI_ASSIGN_TO_FLAT_PORT(s_axi_``name``, req, rsp)


////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Macros instantiating signal highlighter from common verification
// https://github.com/pulp-platform/common_verification.git
// `AXI_HIGHLIGHT(__name, __aw_t, __w_t, __b_t, __ar_t, __r_t, __req, __resp)
`define CALIPTRA_SS_TB_AXI_HIGHLIGHT(__name, __aw_t, __w_t, __b_t, __ar_t, __r_t, __req, __resp) \
  signal_highlighter #(                                                           \
    .T ( __aw_t )                                                                 \
  ) i_signal_highlighter_``__name``_aw (                                          \
    .ready_i ( __resp.aw_ready ),                                                 \
    .valid_i ( __req.aw_valid  ),                                                 \
    .data_i  ( __req.aw        )                                                  \
  );                                                                              \
  signal_highlighter #(                                                           \
    .T ( __w_t )                                                                  \
  ) i_signal_highlighter_``__name``_w (                                           \
    .ready_i ( __resp.w_ready ),                                                  \
    .valid_i ( __req.w_valid  ),                                                  \
    .data_i  ( __req.w        )                                                   \
  );                                                                              \
  signal_highlighter #(                                                           \
    .T ( __b_t )                                                                  \
  ) i_signal_highlighter_``__name``_b (                                           \
    .ready_i ( __req.b_ready  ),                                                  \
    .valid_i ( __resp.b_valid ),                                                  \
    .data_i  ( __resp.b       )                                                   \
  );                                                                              \
  signal_highlighter #(                                                           \
    .T ( __ar_t )                                                                 \
  ) i_signal_highlighter_``__name``_ar (                                          \
    .ready_i ( __resp.ar_ready ),                                                 \
    .valid_i ( __req.ar_valid  ),                                                 \
    .data_i  ( __req.ar        )                                                  \
  );                                                                              \
  signal_highlighter #(                                                           \
    .T ( __r_t )                                                                  \
  ) i_signal_highlighter_``__name``_r (                                           \
    .ready_i ( __req.r_ready  ),                                                  \
    .valid_i ( __resp.r_valid ),                                                  \
    .data_i  ( __resp.r       )                                                   \
  );
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Caliptra SS testbench additions (not part of the pulp-platform/axi upstream).
//
// Connect a Caliptra-RTL style AXI endpoint to a PULP req/resp struct pair.  Caliptra interfaces
// (`axi_if` from caliptra-rtl, or the flat `axi_struct_pkg` wr/rd structs) use flat lowercase
// signal names (awaddr, arvalid, ...) without CACHE/PROT/QOS/REGION/ATOP sideband.  These macros
// adapt the naming, tie the missing fields, and adapt width differences (addr, id, data, strb)
// with self-sizing casts, so the same macro serves 32- and 64-bit endpoints (narrow endpoints use
// byte lanes [3:0] of the 64-bit struct fields by testbench convention).
//
// Manager direction (the Caliptra interface requests, e.g. MCU LSU/IFU/SB, Caliptra DMA, SOC BFM):
// `CALIPTRA_SS_TB_AXI_ASSIGN_FROM_CPTRA_MGR(req, rsp, cptra_if)
//   plus exactly one of (AW/AR cache/prot/qos/region fields):
// `CALIPTRA_SS_TB_AXI_ASSIGN_MGR_SIDEBAND(req, cptra_if)     // from <cptra_if>_awcache etc.
// `CALIPTRA_SS_TB_AXI_ASSIGN_MGR_NO_SIDEBAND(req)            // tie to '0
//
// Subordinate direction (the Caliptra interface responds, e.g. I3C, MCI, SoC IFC, SRAM, SPI, UART):
// `CALIPTRA_SS_TB_AXI_ASSIGN_TO_CPTRA_SUB(rsp, req, cptra_if)
//
// Subordinates with split axi_struct_pkg write/read struct pairs (FC, LCC):
// `CALIPTRA_SS_TB_AXI_ASSIGN_TO_CPTRA_SUB_WR(rsp, req, wr_req, wr_rsp)
// `CALIPTRA_SS_TB_AXI_ASSIGN_TO_CPTRA_SUB_RD(rsp, req, rd_req, rd_rsp)
//
// The per-channel macros are also usable standalone for ports that need special handling on one
// channel (e.g. a read-only subordinate, or an AW channel with an address fixup).
`define CALIPTRA_SS_TB_AXI_ASSIGN_AW_FROM_CPTRA(req, rsp, cptra)      \
  assign req.aw.id      = ($bits(req.aw.id))'(cptra.awid);            \
  assign req.aw.addr    = ($bits(req.aw.addr))'(cptra.awaddr);        \
  assign req.aw.len     = cptra.awlen;                                \
  assign req.aw.size    = cptra.awsize;                               \
  assign req.aw.burst   = cptra.awburst;                              \
  assign req.aw.lock    = cptra.awlock;                               \
  assign req.aw.atop    = '0;                                         \
  assign req.aw.user    = cptra.awuser;                               \
  assign req.aw_valid   = cptra.awvalid;                              \
  assign cptra.awready  = rsp.aw_ready;
`define CALIPTRA_SS_TB_AXI_ASSIGN_W_FROM_CPTRA(req, rsp, cptra)       \
  assign req.w.data     = ($bits(req.w.data))'(cptra.wdata);          \
  assign req.w.strb     = ($bits(req.w.strb))'(cptra.wstrb);          \
  assign req.w.last     = cptra.wlast;                                \
  assign req.w.user     = cptra.wuser;                                \
  assign req.w_valid    = cptra.wvalid;                               \
  assign cptra.wready   = rsp.w_ready;
`define CALIPTRA_SS_TB_AXI_ASSIGN_B_TO_CPTRA(req, rsp, cptra)         \
  assign cptra.bid      = ($bits(cptra.bid))'(rsp.b.id);              \
  assign cptra.bresp    = rsp.b.resp;                                 \
  assign cptra.buser    = rsp.b.user;                                 \
  assign cptra.bvalid   = rsp.b_valid;                                \
  assign req.b_ready    = cptra.bready;
`define CALIPTRA_SS_TB_AXI_ASSIGN_AR_FROM_CPTRA(req, rsp, cptra)      \
  assign req.ar.id      = ($bits(req.ar.id))'(cptra.arid);            \
  assign req.ar.addr    = ($bits(req.ar.addr))'(cptra.araddr);        \
  assign req.ar.len     = cptra.arlen;                                \
  assign req.ar.size    = cptra.arsize;                               \
  assign req.ar.burst   = cptra.arburst;                              \
  assign req.ar.lock    = cptra.arlock;                               \
  assign req.ar.user    = cptra.aruser;                               \
  assign req.ar_valid   = cptra.arvalid;                              \
  assign cptra.arready  = rsp.ar_ready;
`define CALIPTRA_SS_TB_AXI_ASSIGN_R_TO_CPTRA(req, rsp, cptra)         \
  assign cptra.rid      = ($bits(cptra.rid))'(rsp.r.id);              \
  assign cptra.rdata    = ($bits(cptra.rdata))'(rsp.r.data);          \
  assign cptra.rresp    = rsp.r.resp;                                 \
  assign cptra.rlast    = rsp.r.last;                                 \
  assign cptra.ruser    = rsp.r.user;                                 \
  assign cptra.rvalid   = rsp.r_valid;                                \
  assign req.r_ready    = cptra.rready;
`define CALIPTRA_SS_TB_AXI_ASSIGN_FROM_CPTRA_MGR(req, rsp, cptra)     \
  `CALIPTRA_SS_TB_AXI_ASSIGN_AW_FROM_CPTRA(req, rsp, cptra)           \
  `CALIPTRA_SS_TB_AXI_ASSIGN_W_FROM_CPTRA(req, rsp, cptra)            \
  `CALIPTRA_SS_TB_AXI_ASSIGN_B_TO_CPTRA(req, rsp, cptra)              \
  `CALIPTRA_SS_TB_AXI_ASSIGN_AR_FROM_CPTRA(req, rsp, cptra)           \
  `CALIPTRA_SS_TB_AXI_ASSIGN_R_TO_CPTRA(req, rsp, cptra)
`define CALIPTRA_SS_TB_AXI_ASSIGN_MGR_SIDEBAND(req, cptra)            \
  assign req.aw.cache   = cptra``_awcache;                            \
  assign req.aw.prot    = cptra``_awprot;                             \
  assign req.aw.qos     = cptra``_awqos;                              \
  assign req.aw.region  = cptra``_awregion;                           \
  assign req.ar.cache   = cptra``_arcache;                            \
  assign req.ar.prot    = cptra``_arprot;                             \
  assign req.ar.qos     = cptra``_arqos;                              \
  assign req.ar.region  = cptra``_arregion;
`define CALIPTRA_SS_TB_AXI_ASSIGN_MGR_NO_SIDEBAND(req)                \
  assign req.aw.cache   = '0;                                         \
  assign req.aw.prot    = '0;                                         \
  assign req.aw.qos     = '0;                                         \
  assign req.aw.region  = '0;                                         \
  assign req.ar.cache   = '0;                                         \
  assign req.ar.prot    = '0;                                         \
  assign req.ar.qos     = '0;                                         \
  assign req.ar.region  = '0;
`define CALIPTRA_SS_TB_AXI_ASSIGN_AW_TO_CPTRA(rsp, req, cptra)        \
  assign cptra.awid     = ($bits(cptra.awid))'(req.aw.id);            \
  assign cptra.awaddr   = ($bits(cptra.awaddr))'(req.aw.addr);        \
  assign cptra.awlen    = req.aw.len;                                 \
  assign cptra.awsize   = req.aw.size;                                \
  assign cptra.awburst  = req.aw.burst;                               \
  assign cptra.awlock   = req.aw.lock;                                \
  assign cptra.awuser   = req.aw.user;                                \
  assign cptra.awvalid  = req.aw_valid;                               \
  assign rsp.aw_ready   = cptra.awready;
`define CALIPTRA_SS_TB_AXI_ASSIGN_W_TO_CPTRA(rsp, req, cptra)         \
  assign cptra.wdata    = ($bits(cptra.wdata))'(req.w.data);          \
  assign cptra.wstrb    = ($bits(cptra.wstrb))'(req.w.strb);          \
  assign cptra.wlast    = req.w.last;                                 \
  assign cptra.wuser    = req.w.user;                                 \
  assign cptra.wvalid   = req.w_valid;                                \
  assign rsp.w_ready    = cptra.wready;
`define CALIPTRA_SS_TB_AXI_ASSIGN_B_FROM_CPTRA(rsp, req, cptra)       \
  assign rsp.b.id       = ($bits(rsp.b.id))'(cptra.bid);              \
  assign rsp.b.resp     = cptra.bresp;                                \
  assign rsp.b.user     = cptra.buser;                                \
  assign rsp.b_valid    = cptra.bvalid;                               \
  assign cptra.bready   = req.b_ready;
`define CALIPTRA_SS_TB_AXI_ASSIGN_AR_TO_CPTRA(rsp, req, cptra)        \
  assign cptra.arid     = ($bits(cptra.arid))'(req.ar.id);            \
  assign cptra.araddr   = ($bits(cptra.araddr))'(req.ar.addr);        \
  assign cptra.arlen    = req.ar.len;                                 \
  assign cptra.arsize   = req.ar.size;                                \
  assign cptra.arburst  = req.ar.burst;                               \
  assign cptra.arlock   = req.ar.lock;                                \
  assign cptra.aruser   = req.ar.user;                                \
  assign cptra.arvalid  = req.ar_valid;                               \
  assign rsp.ar_ready   = cptra.arready;
`define CALIPTRA_SS_TB_AXI_ASSIGN_R_FROM_CPTRA(rsp, req, cptra)       \
  assign rsp.r.id       = ($bits(rsp.r.id))'(cptra.rid);              \
  assign rsp.r.data     = ($bits(rsp.r.data))'(cptra.rdata);          \
  assign rsp.r.resp     = cptra.rresp;                                \
  assign rsp.r.last     = cptra.rlast;                                \
  assign rsp.r.user     = cptra.ruser;                                \
  assign rsp.r_valid    = cptra.rvalid;                               \
  assign cptra.rready   = req.r_ready;
`define CALIPTRA_SS_TB_AXI_ASSIGN_TO_CPTRA_SUB(rsp, req, cptra)       \
  `CALIPTRA_SS_TB_AXI_ASSIGN_AW_TO_CPTRA(rsp, req, cptra)             \
  `CALIPTRA_SS_TB_AXI_ASSIGN_W_TO_CPTRA(rsp, req, cptra)              \
  `CALIPTRA_SS_TB_AXI_ASSIGN_B_FROM_CPTRA(rsp, req, cptra)            \
  `CALIPTRA_SS_TB_AXI_ASSIGN_AR_TO_CPTRA(rsp, req, cptra)             \
  `CALIPTRA_SS_TB_AXI_ASSIGN_R_FROM_CPTRA(rsp, req, cptra)
// Split write/read struct pairs (axi_struct_pkg, used by FC and LCC) carry no W/B/R user fields:
// WUSER is dropped, B/RUSER are tied '0 toward the crossbar.
`define CALIPTRA_SS_TB_AXI_ASSIGN_TO_CPTRA_SUB_WR(rsp, req, wr_req, wr_rsp) \
  assign wr_req.awid    = ($bits(wr_req.awid))'(req.aw.id);           \
  assign wr_req.awaddr  = ($bits(wr_req.awaddr))'(req.aw.addr);       \
  assign wr_req.awlen   = req.aw.len;                                 \
  assign wr_req.awsize  = req.aw.size;                                \
  assign wr_req.awburst = req.aw.burst;                               \
  assign wr_req.awlock  = req.aw.lock;                                \
  assign wr_req.awuser  = req.aw.user;                                \
  assign wr_req.awvalid = req.aw_valid;                               \
  assign rsp.aw_ready   = wr_rsp.awready;                             \
  assign wr_req.wdata   = ($bits(wr_req.wdata))'(req.w.data);         \
  assign wr_req.wstrb   = ($bits(wr_req.wstrb))'(req.w.strb);         \
  assign wr_req.wlast   = req.w.last;                                 \
  assign wr_req.wvalid  = req.w_valid;                                \
  assign rsp.w_ready    = wr_rsp.wready;                              \
  assign rsp.b.id       = ($bits(rsp.b.id))'(wr_rsp.bid);             \
  assign rsp.b.resp     = wr_rsp.bresp;                               \
  assign rsp.b.user     = '0;                                         \
  assign rsp.b_valid    = wr_rsp.bvalid;                              \
  assign wr_req.bready  = req.b_ready;
`define CALIPTRA_SS_TB_AXI_ASSIGN_TO_CPTRA_SUB_RD(rsp, req, rd_req, rd_rsp) \
  assign rd_req.arid    = ($bits(rd_req.arid))'(req.ar.id);           \
  assign rd_req.araddr  = ($bits(rd_req.araddr))'(req.ar.addr);       \
  assign rd_req.arlen   = req.ar.len;                                 \
  assign rd_req.arsize  = req.ar.size;                                \
  assign rd_req.arburst = req.ar.burst;                               \
  assign rd_req.arlock  = req.ar.lock;                                \
  assign rd_req.aruser  = req.ar.user;                                \
  assign rd_req.arvalid = req.ar_valid;                               \
  assign rsp.ar_ready   = rd_rsp.arready;                             \
  assign rsp.r.id       = ($bits(rsp.r.id))'(rd_rsp.rid);             \
  assign rsp.r.data     = ($bits(rsp.r.data))'(rd_rsp.rdata);         \
  assign rsp.r.resp     = rd_rsp.rresp;                               \
  assign rsp.r.last     = rd_rsp.rlast;                               \
  assign rsp.r.user     = '0;                                         \
  assign rsp.r_valid    = rd_rsp.rvalid;                              \
  assign rd_req.rready  = req.r_ready;
////////////////////////////////////////////////////////////////////////////////////////////////////

`endif
