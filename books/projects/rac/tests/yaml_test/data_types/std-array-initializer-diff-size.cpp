#include <array>
using namespace std;

// RAC begin

int foo() {
  array<int, 3> a = {{ 2, 4 }};
  return a[2];
}

// RAC end
