#include "ac_int.h"

// RAC begin

typedef ac_int<32, false> ui32;
typedef ac_int<64, false> ui64;

tuple<ui32, ui64> foo() {
  return tuple<ui32, ui64>(0, 0);
}

// RAC end
