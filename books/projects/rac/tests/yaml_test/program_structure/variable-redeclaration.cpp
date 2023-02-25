#include "ac_int.h"

// RAC begin

typedef ac_int<2, true> int2;

int foo()
{
    int a = 2;
    int2 a = 3;
    return a;
}

// RAC end
