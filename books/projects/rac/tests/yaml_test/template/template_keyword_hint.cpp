#include <ac_int.h>

// RAC begin

template <int n>
int foo(ac_int<64, false> x) {
  return x.slc<n>(0);
}
