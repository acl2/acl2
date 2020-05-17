// Copyright (C) 2020 David S. Hardin
//
// License: (An MIT/X11-style license)
//
//   Permission is hereby granted, free of charge, to any person obtaining a
//   copy of this software and associated documentation files (the "Software"),
//   to deal in the Software without restriction, including without limitation
//   the rights to use, copy, modify, merge, publish, distribute, sublicense,
//   and/or sell copies of the Software, and to permit persons to whom the
//   Software is furnished to do so, subject to the following conditions:
//
//   The above copyright notice and this permission notice shall be included in
//   all copies or substantial portions of the Software.
//
//   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.


#ifndef _RAC_SETUP

#include <iostream>
#include <ac_int.h>
#include <rac.h>

using namespace std;

typedef unsigned long uint64; // Just used to facilitate printing

// RAC begin

typedef ac_int<1,false> ui1;
typedef ac_int<2,false> ui2;
typedef ac_int<3,false> ui3;
typedef ac_int<4,false> ui4;
typedef ac_int<5,false> ui5;
typedef ac_int<6,false> ui6;
typedef ac_int<7,false> ui7;
typedef ac_int<8,false> ui8;
typedef ac_int<9,false> ui9;
typedef ac_int<11,false> ui11;
typedef ac_int<12,false> ui12;
typedef ac_int<13,false> ui13;
typedef ac_int<14,false> ui14;
typedef ac_int<15,false> ui15;
typedef ac_int<16,false> ui16;
typedef ac_int<17,false> ui17;
typedef ac_int<18,false> ui18;
typedef ac_int<19,false> ui19;
typedef ac_int<20,false> ui20;
typedef ac_int<21,false> ui21;
typedef ac_int<23,false> ui23;
typedef ac_int<24,false> ui24;
typedef ac_int<25,false> ui25;
typedef ac_int<32,false> ui32;
typedef ac_int<32,true> i32;
typedef ac_int<64,false> ui64;
typedef ac_int<64,true> i64;

#define _RAC_SETUP

#else
#endif

//#define BIG_STRUCT

#ifdef BIG_STRUCT
#define STYP void
#define SVAL 
#define amp(x) &x
#define SASN
#else
#define STYP STKObj
#define SVAL SObj
#define amp(x) x
#define SASN SObj =
#endif

#define STK_MAX_SZ 16383

#define STK_OK 0
#define STK_OCCUPANCY_ERR 255


struct STKObj {
  ui14 nodeTop;
  array<i64, STK_MAX_SZ> nodeArr;
};


#ifdef COMPILE_ME

#ifndef _STK_BODY

STYP STK_init (STKObj amp(SObj));

STYP STK_initAll (STKObj amp(SObj));

ui14 STK_capacity (STKObj amp(SObj));

bool STK_isEmpty (STKObj amp(SObj));

ui14 STK_sz (STKObj amp(SObj));

ui14 STK_space (STKObj amp(SObj));

STYP STK_pop (STKObj amp(SObj));

STYP STK_popTo (i64 datum, STKObj amp(SObj));

tuple<ui8, i64> STK_top (STKObj amp(SObj));

tuple<ui8, i64> STK_topThenPop (STKObj amp(SObj));

tuple<ui8, i64> STK_next (STKObj amp(SObj));

STYP STK_push (i64 n, STKObj amp(SObj));

#else
#endif

#else
#endif
