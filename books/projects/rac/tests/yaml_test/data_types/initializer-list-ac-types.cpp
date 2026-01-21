#include <ac_int.h>
#include <array>
#include <tuple>

using namespace std;

// RAC begin

typedef ac_int<2, false> ui2;

tuple<ui2, ui2> foo() {
  tuple<ui2, ui2> t = { 1, 4 };
  return t;
}

array<ui2, 2> bar() {
  array<ui2, 2> t = {{ 1, 4 }};
  return t;
}

// RAC end
