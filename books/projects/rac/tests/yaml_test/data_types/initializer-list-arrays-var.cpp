#include <ac_int.h>

// RAC begin

typedef ac_int<2, false> ui2;

ui2 foo() {
  int x = 2;
  ui2 arr[2] = {1, x};
  return arr[1];
}
