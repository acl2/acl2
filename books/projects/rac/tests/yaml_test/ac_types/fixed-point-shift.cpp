#include "ac_fixed.h"

// RAC begin

int rshift(ac_fixed<4, 3, false> x)
{
  return x << 2;
}

int lshift(ac_fixed<4, 3, false> x)
{
  return x >> 2;
}

// RAC end
