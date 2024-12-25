#include "ac_int.h"

// RAC begin

template <int n, bool s>
int slc_test() {
  ac_int<n, s> x = 4;
  return x;
}

int main() { return slc_test<4, true>(); }
