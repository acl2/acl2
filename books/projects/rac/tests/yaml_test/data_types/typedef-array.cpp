#include <array>
using namespace std;

// RAC begin

typedef array<int, 5> u5;

u5 foo() {
  u5 a = {{}};
  a[2] = 2;
  return a;
}

// RAC end
