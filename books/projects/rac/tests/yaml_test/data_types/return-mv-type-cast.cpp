#include <ac_int.h>
#include <array>
#include <tuple>

using namespace std;

// RAC begin

typedef ac_int<2, false> ui2;
typedef ac_int<3, false> ui3;

tuple<ui3, ui3> foo(ui3 x) {

  return tuple<ui3, ui3>(x, x);
}

bool bar () {
  ui2 x = 0, y = 0;
  tie(x, y) = foo(3);
  return true;
}

// RAC end
