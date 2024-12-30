#include "rac.h"

// The testsuite does not fully preprocess so we are doing it with the
// preprocessor instead.
#define assert(x) __RAC_ASSERT(x)

// RAC begin

int foo(int a)
{
  assert(a);
  return 1;
}

// RAC end
