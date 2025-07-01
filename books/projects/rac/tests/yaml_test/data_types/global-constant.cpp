#include <array>
using namespace std;

// RAC begin

enum Num { ONE, TWO };
const Num n = ONE;

struct S {
  int a;
};
const S s = { 3 };

const int a = 2;
const int b = 2;

const int arr[4] = { 1, 2, 3, 4 };
const array<int, 2> std_arr = {{ 1, 2 }};

int foo() { return a + s.a + n; }

int bar() {
  const int c = 4, e = 4, f = 4;
  return arr[3];
}

// RAC end
