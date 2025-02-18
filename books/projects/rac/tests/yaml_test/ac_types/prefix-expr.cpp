#include <ac_int.h>

// RAC begin

typedef ac_int<4, false> ui4;

int foo(ui4 x) {

  int a = +x;
  int b = -x;
  bool c = !x;
  return 0;
}
