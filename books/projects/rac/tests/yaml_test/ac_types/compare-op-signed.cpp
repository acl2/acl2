#include "ac_int.h"

// RAC begin

typedef ac_int<32, true> si32;

bool foo() {
  si32 x = -1;
  return (x <= 0);
}

// RAC end
