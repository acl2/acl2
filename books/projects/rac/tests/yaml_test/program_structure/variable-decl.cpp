#include <ac_int.h>
#include <ac_fixed.h>
#include <array>

using namespace std;

// RAC begin

int foo()
{
  ac_int<2, false> a1 = 1;
  ac_int<2, true> a2 = -4;
  ac_fixed<2, 4, false> b1 = 1;
  ac_fixed<2, 4, true> b2 = -2;
  int c = 9;
  array<int, 4> d;
  int64 e = 4;
  uint64 f = 4;

  int g[3];
  int h[3] = {1, 2, 3};

  return 0;
}

// RAC end
