#include <ac_int.h>

// RAC begin

typedef ac_int<4, false> MyType;

int foo() {

  const MyType a = 2;
  MyType b[3] = {};
  b[1] = 4;
  return b[1];
}
