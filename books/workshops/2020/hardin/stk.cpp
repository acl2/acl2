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
  SObj.nodeTop = STK_MAX_NODE1;

  return SVAL;
}


// Restore to factory defaults

STYP STK_initAll (STKObj amp(SObj)) {
  SObj.nodeTop = STK_MAX_NODE1;
  for (uint i = 0; i < STK_MAX_NODE1; i++) {
    SObj.nodeArr[i] = 0;
  }
  return SVAL;
}


tuple<ui8, i64> STK_top (STKObj amp(SObj)) {
  if (SObj.nodeTop == STK_MAX_NODE1) {
    return tuple<ui8, i64>(STK_OCCUPANCY_ERR, 0);
  } else {
    return tuple<ui8, i64>(STK_OK, SObj.nodeArr[SObj.nodeTop]);
  }
}


tuple<ui8, i64> STK_next (STKObj amp(SObj)) {
  if ((STK_MAX_NODE1 - SObj.nodeTop) < 2) {
    return tuple<ui8, i64>(STK_OCCUPANCY_ERR, 0);
  } else {
    return tuple<ui8, i64>(STK_OK, SObj.nodeArr[SObj.nodeTop + 1]);
  }
}


ui14 STK_sz (STKObj amp(SObj)) {
  return (STK_MAX_NODE1 - SObj.nodeTop);
}


ui14 STK_space (STKObj amp(SObj)) {
  return SObj.nodeTop;
}


// Remove from head of list

STYP STK_pop (STKObj amp(SObj)) {
  if (SObj.nodeTop == STK_MAX_NODE1) {
    return SVAL;
  } else {
    SObj.nodeTop++;
    return SVAL;
  }
}


STYP STK_popTo (i64 datum, STKObj amp(SObj)) {
  if ((STK_MAX_NODE1 - SObj.nodeTop) == 0) {
    return SVAL;
  } else {
    ui14 d = 0;
    uint i;
    for (i = 0;
         ((i < (STK_MAX_NODE1 - SObj.nodeTop)) &&
          SObj.nodeArr[i+ SObj.nodeTop] != datum);
         i++) {
      d++;
    }
    SObj.nodeTop += d;
    return SVAL;
  }
}


// Push to top of stack

STYP STK_push (i64 v, STKObj amp(SObj)) {
  if (SObj.nodeTop == 0) {
    return SVAL;
  } else {
    SObj.nodeTop--;
    SObj.nodeArr[SObj.nodeTop] = v;
    return SVAL;
  }
}
