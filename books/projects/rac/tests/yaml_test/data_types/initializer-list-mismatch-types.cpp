#include <array>
using namespace std;

// RAC begin

struct S {
  int a;
};

int foo() {
  array<int, 3> a = {{}};
  S s = { a };
  return 0;
}

int bar() {
  S s = { 1, 2 };
  return 0;
}
