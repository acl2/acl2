#include "ac_int.h"

// RAC begin

typedef ac_int<2, false> ui2;

int foo(ui2 f)
{
  return f;
}

// RAC end
