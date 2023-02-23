#include "ac_int.h"

// RAC begin

int set_two(ac_int<2, false> x)
{
  x.set_slc(1, x.slc<0>(0));

  return 0;
}

// RAC end
