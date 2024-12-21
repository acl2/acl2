#include <array>
#include <tuple>
using namespace std;

// RAC begin

tuple<int, int> foo() { return tuple<int, int>(3, 2); }

int bar() {
  int a = 0, b = foo();
  return 0;
}

// RAC end
