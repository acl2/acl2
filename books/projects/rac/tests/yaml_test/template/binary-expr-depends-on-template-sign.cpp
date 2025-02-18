#include <ac_int.h>

// RAC begin

template <bool S>
int foo(ac_int<4, S> x) {
  return x + 1;
}

// RAC end

#include <iostream>

int main() {

  std::cout << foo<false>(0) << ' '
    << foo<true>(0) << ' '
    << foo<false>(14) << ' '
    << foo<true>(14) << ' '
    << foo<false>(9) << ' '
    << foo<true>(9);
}
