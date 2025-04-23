#include <ac_int.h>
#include <tuple>

using namespace std;

// RAC begin

typedef ac_int<64, false> ui64;


tuple<ui64, ui64> foo() {
  return tuple<ui64, ui64>(0, 0);
}

int main() {

  ui64 a, b;
  tie(a, b) = foo();
  return 0;
}
