#include <ac_int.h>

// RAC begin

typedef ac_int<32, true> si32;
typedef ac_int<32, false> ui32;
si32 foo() {
  si32 x = -1;
  ui32 y = (x >> 31) + 1;
  return y;
}
