#include "ac_int.h"

// RAC begin

ac_int<32, false> get_pos(ac_int<32, false> x)
{
  return x.slc<0xF>(0);
}

// RAC end
