#include <ac_int.h>

// RAC begin

typedef ac_int<10, true> si10;
typedef ac_int<32, true> si32;

int foo(si10 si10_val, si32 si32_val) {

  int a = si10(10);
  int b = si32(10);

  uint a2 = si10(10);
  uint b2 = si32(10);

  si32 c = si10_val;
  si10 d = si32_val;

  si32 f = c * d;

  return f;
}

// RAC end
