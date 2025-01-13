#include "ac_int.h"

// RAC begin

typedef ac_int<8, false> u8;

int adder(u8 a, u8 b) {
  int res = 0;
  for (res = b; a != 0; a--)
    res++;

  return res;
}

// RAC end
