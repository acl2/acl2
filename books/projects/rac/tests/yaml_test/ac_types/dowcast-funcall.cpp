#include "ac_int.h"

// RAC begin

typedef ac_int<2, false> ui2;
typedef ac_int<62, false> ui62;

int foo(ui2 f) { return f; }
int bar(ui62 f) { return f; }
int main() { return foo(255) + bar(255); }

// RAC end
