#include <ac_int.h>
#include <array>

using namespace std;

// RAC begin

int binary_invalid(int a, array<int, 3> b) { return a && b; }

int prefix_invalid() {
  array<int, 3> a = {{ 0, 1, 2 }};
  return -a;
}

int no_implicit_cast() {
  ac_int<3, false> x = 0;
  array<int, 3> a = {{ 0, 1, 2 }};
  x = x + a;

  return 0;
}

int ternary_invalid() {
  ac_int<3, false> x = 0;
  array<int, 3> a = {{ 0, 1, 2 }};
  x = true ? x : a;

  return 0;
}

typedef array<int, 3> array3;
int prefix_invalid_with_typedef() {
  array3 a = {{ 0, 1, 2 }};
  return -a;
}

// RAC end
