#include <array>
using namespace std;

// RAC begin

struct S1 {
  array<int, 4> a;
};

struct S2 {
  int a[4];
};

int foo() {

  S1 s1;
  s1.a[3] = 1;
  return s1.a[3];
}

int bar() {

  S2 s2;
  s2.a[3] = 1;
  return s2.a[3];
}
