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


// RAC example: Simple Array-Based Stack

// Note: Stack grows from high array indices to low array indices for convenience

#define _STK_BODY

#include "stk.h"


////////////////////////////////////////////////////////////////////////////////
//
// Stack (STK) operators
// 

// Initialize 'just enough' state

STYP STK_init (STKObj amp(SObj)) {
  SObj.nodeTop = STK_MAX_SZ;

  return SVAL;
}


// Restore to factory defaults

STYP STK_initAll (STKObj amp(SObj)) {
  SObj.nodeTop = STK_MAX_SZ;
  for (uint i = 0; i < STK_MAX_SZ; i++) {
    SObj.nodeArr[i] = 0;
  }
  return SVAL;
}

ui14 STK_capacity (STKObj amp(SObj)) {
  return STK_MAX_SZ;
}

bool STK_isEmpty (STKObj amp(SObj)) {
  return (STK_MAX_SZ == SObj.nodeTop);
}

ui14 STK_sz (STKObj amp(SObj)) {
  return (STK_MAX_SZ - SObj.nodeTop);
}

ui14 STK_space (STKObj amp(SObj)) {
  return SObj.nodeTop;
}


// Pop the top of stack

STYP STK_pop (STKObj amp(SObj)) {
  if (SObj.nodeTop < STK_MAX_SZ) {
    SObj.nodeTop++;
  }
  return SVAL;
}

STYP STK_popTo (i64 datum, STKObj amp(SObj)) {
  if ((STK_MAX_SZ - SObj.nodeTop) == 0) {
    return SVAL;
  } else {
    ui14 d = 0;
    uint i;
    for (i = 0;
         ((i < (STK_MAX_SZ - SObj.nodeTop)) &&
          SObj.nodeArr[i+ SObj.nodeTop] != datum);
         i++) {
      d++;
    }
    SObj.nodeTop += d;
    return SVAL;
  }
}


tuple<ui8, i64> STK_top (STKObj amp(SObj)) {
  if (SObj.nodeTop < STK_MAX_SZ) {
    return tuple<ui8, i64>(STK_OK, SObj.nodeArr[SObj.nodeTop]);
  } else {
    return tuple<ui8, i64>(STK_OCCUPANCY_ERR, 0);
  }
}

tuple<ui8, i64> STK_topThenPop (STKObj amp(SObj)) {
  if (SObj.nodeTop < STK_MAX_SZ) {
    i64 tos = SObj.nodeArr[SObj.nodeTop];
    SObj.nodeTop++;
    return tuple<ui8, i64>(STK_OK, tos);
  } else {
    return tuple<ui8, i64>(STK_OCCUPANCY_ERR, 0);
  }
}

tuple<ui8, i64> STK_next (STKObj amp(SObj)) {
  if ((STK_MAX_SZ - SObj.nodeTop) < 2) {
    return tuple<ui8, i64>(STK_OCCUPANCY_ERR, 0);
  } else {
    return tuple<ui8, i64>(STK_OK, SObj.nodeArr[SObj.nodeTop + 1]);
  }
}


// Push to top of stack

STYP STK_push (i64 v, STKObj amp(SObj)) {
  if (SObj.nodeTop != 0) {
    SObj.nodeTop--;
    SObj.nodeArr[SObj.nodeTop] = v;
  }
  return SVAL;
}
