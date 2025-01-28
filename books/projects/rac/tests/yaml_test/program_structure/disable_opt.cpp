#include <ac_int.h>

typedef unsigned uint;

// RAC begin

typedef ac_int<8, false> ui8;
typedef ac_int<32, false> ui32;

uint foo(ui8 x) { return x; } // Cast can be optimized away.
ui8 bar(uint x) { return x; } // Never optimized away.

ui32 foo2(ui8 x) { return x; } // Cast can be optimized away.
ui8 bar2(ui32 x) { return x; } // Never optimized away.

// RAC end
