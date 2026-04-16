#include <array>
#include <tuple>
using namespace std;

// RAC begin

tuple<int, int> foo() {
  return tuple<int, int>(2, 1);
}

int main() {
  array<int, 1> a = {{ 0 }};
  int x = 0;
  tie(x, a[0]) = foo();
  return 0;
}
