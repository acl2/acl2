#include "ac_int.h"
#include "ac_fixed.h"

// RAC begin

ac_int<32, false> get_set_unsigned(ac_int<32, false> x)
{
  x.set_slc(0, x.slc<4>(10));
  return x;
}

ac_int<32, true> get_set_signed(ac_int<32, true> x)
{
  x.set_slc(0, x.slc<4>(10));
  return x;
}

ac_fixed<16, 16, false> get_set_fixed_unsigned(ac_fixed<16, 16, false> x)
{
  x.set_slc(0, x.slc<4>(10));
  return x;
}

ac_fixed<16, 16, true> get_set_fixed_signed(ac_fixed<16, 16, true> x)
{
  x.set_slc(0, x.slc<4>(10));
  return x;
}

ac_int<16, false> set_single(ac_int<16, false> x)
{
  ac_int<1, false> y = x[10];
  x.set_slc(0, y);
  return x;
}

ac_fixed<16, 16, true> get_set_same(ac_fixed<16, 16, true> x)
{
  x = x;
  return x;
}

// RAC end
