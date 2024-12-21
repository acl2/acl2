#include "ac_int.h"

// RAC begin

ac_int<32, false> get_set_unsigned(ac_int<32, false> x) {
  x.set_slc(0, x.slc<4>(10));
  return x;
}

ac_int<32, true> get_set_signed(ac_int<32, true> x) {
  x.set_slc(0, x.slc<4>(10));
  return x;
}

ac_int<16, false> set_single(ac_int<16, false> x) {
  ac_int<1, false> y = x[10];
  x.set_slc(0, y);
  return x;
}

// RAC end

#include <iostream>

int main() {

  std::cout << get_set_signed(4) << '\n'
            << get_set_signed(255) << '\n'
            << get_set_signed(-1) << '\n'
            << get_set_signed(-8) << '\n';
}
