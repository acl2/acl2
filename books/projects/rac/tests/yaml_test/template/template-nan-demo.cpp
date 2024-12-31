#include "ac_int.h"
#undef assert
void assert(bool) {}

typedef unsigned uint;

// RAC begin

template <uint manw, uint expw>
bool is_nan(ac_int<manw + expw + 1, false> x) {

  bool is_exp_saturated = x.template slc<expw>(manw) == (1 << expw) - 1;
  bool is_man_zero = x.template slc<manw>(0) == 0;
  return is_exp_saturated && !is_man_zero;
}

int main() {

  bool sp_nan = is_nan<23, 8>(0xFFFFFFFF);
  bool sp_not_nan = is_nan<23, 8>(0x00000000);

  bool dp_nan = is_nan<52, 10>(0xFFFFFFFFFFFFFFFF);
  bool dp_not_nan = is_nan<52, 11>(0xFFFFFFFF);

  assert(sp_nan);
  assert(!sp_not_nan);

  assert(dp_nan);
  assert(!dp_not_nan);

  return 0;
}
