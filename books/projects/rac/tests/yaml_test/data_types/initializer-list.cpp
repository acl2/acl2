#include <array>
using namespace std;

// RAC begin

array<int, 2> bar() {
  array<int, 2> t = { 1, 2 };
  return t;
}

struct S {
  int a;
  int b;
};

S foo() {
  S s = { 3, 4 };
  return s;
}

// RAC end
