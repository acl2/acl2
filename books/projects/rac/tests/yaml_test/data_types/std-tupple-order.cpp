#include <ac_int.h>
#include <tuple>

using namespace std;

// RAC begin

typedef ac_int<8, false> ui8;
typedef ac_int<4, false> ui4;
typedef ac_int<2, false> ui2;

tuple<ui4, ui2> foo(ui8 a) { return tuple<ui4, ui2>(a, a); }

// RAC end
