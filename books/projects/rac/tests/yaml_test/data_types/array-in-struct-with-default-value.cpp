#include <array>
using namespace std;

// RAC begin

struct S1 {
  array<int, 4> a = {{1, 2, 3, 4}};
};

int foo() {

  S1 s1 = {};
  s1.a[3] = 1;
  return s1.a[3];
}

int bar() {

  S1 s1;
  s1.a[3] = 1;
  return s1.a[3];
}

