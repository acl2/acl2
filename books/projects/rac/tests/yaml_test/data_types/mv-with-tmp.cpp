#include <array>
#include <tuple>
using namespace std;

// RAC begin

tuple<int, int> foo() {
  return tuple<int, int>(2, 1);
}

int main() {
  array<int, 2> a = {{ 0, 0 }};
  tie(a[0], a[1]) = foo();
  return 0;
}
