#include "ac_int.h"

// RAC begin

typedef ac_int<8, false> u8;

u8 adder(u8 a, u8 b)
{
  u8 res;
  for (res = b; a != 0; a--)
    res++;
 
  return res;
}

// RAC end
