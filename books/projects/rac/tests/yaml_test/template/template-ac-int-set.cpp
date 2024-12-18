#include "ac_int.h"

// RAC begin

template <int n>
int set_test(ac_int<n, false> x) {

  x.set_slc(0, ac_int<n / 2, false>(0));
  x.set_slc(n / 2, ac_int<n / 2, false>(0xFFFFFFFF));

  return x;
}

int main() { return set_test<4>(5); }
