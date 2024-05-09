#include "ac_int.h"

// RAC begin

typedef ac_int<4, false> ui4;
typedef ac_int<3, true> si3;
typedef ac_int<4, true> si4;

si4 foo() { return si3(4); }

ui4 bar() { return si3(4); }

// RAC end
