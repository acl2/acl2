#include "ac_int.h"

// RAC begin

int get(ac_int<4, false> x)
{
  x[2] = 0;
  return x;
}

// RAC end
