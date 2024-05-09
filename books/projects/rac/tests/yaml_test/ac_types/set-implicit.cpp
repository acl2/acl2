#include "ac_int.h"

// RAC begin

ac_int<32, false> set_two(ac_int<2, false> x)
{
  x.set_slc(0, x);
  return x;
}

// RAC end
