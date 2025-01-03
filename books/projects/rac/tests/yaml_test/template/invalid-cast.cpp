#include <ac_int.h>
using namespace std;

// RAC begin

template <int N>
int foo(ac_int<N, false> x) {
  return (int)x;
}

// RAC end
