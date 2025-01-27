#include <ac_int.h>

// RAC begin

typedef ac_int<8, true> si8;
typedef ac_int<8, false> ui8;

int foo(bool bsigned, ui8 b) {

  int bval = bsigned ? int(si8(b)) : int(b);
  return bval;
}

// RAC end

#include <iostream>

int main() {

  std::cout << foo(1, 0) << ' ' << foo(1, 255) << ' ' << foo(1, 127) << '\n';
}
